-- Prove2me | solution 1 for syracuse_descends_range_1539967_1541467
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:06.550498+00:00
-- url     : https://prove2.me/submissions/3958c1e2-c35f-4d2e-8ffc-2948d203a70b

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


theorem B2310149 : Blo 1539967 2310149 := bbase (se 4 (by rfl) ⟨216576, by rfl⟩ : syracuseStep 2310149 = 433153) (by norm_num)
theorem B2310173 : Blo 1539967 2310173 := bbase (se 3 (by rfl) ⟨433157, by rfl⟩ : syracuseStep 2310173 = 866315) (by norm_num)
theorem B2924581 : Blo 1539967 2924581 := bbase (se 4 (by rfl) ⟨274179, by rfl⟩ : syracuseStep 2924581 = 548359) (by norm_num)
theorem B3465269 : Blo 1539967 3465269 := bbase (se 5 (by rfl) ⟨162434, by rfl⟩ : syracuseStep 3465269 = 324869) (by norm_num)
theorem B2310197 : Blo 1539967 2310197 := bbase (se 5 (by rfl) ⟨108290, by rfl⟩ : syracuseStep 2310197 = 216581) (by norm_num)
theorem B1949761 : Blo 1539967 1949761 := bbase (se 2 (by rfl) ⟨731160, by rfl⟩ : syracuseStep 1949761 = 1462321) (by norm_num)
theorem B3899461 : Blo 1539967 3899461 := bbase (se 4 (by rfl) ⟨365574, by rfl⟩ : syracuseStep 3899461 = 731149) (by norm_num)
theorem B2310221 : Blo 1539967 2310221 := bbase (se 3 (by rfl) ⟨433166, by rfl⟩ : syracuseStep 2310221 = 866333) (by norm_num)
theorem B7610453 : Blo 1539967 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B2310245 : Blo 1539967 2310245 := bbase (se 4 (by rfl) ⟨216585, by rfl⟩ : syracuseStep 2310245 = 433171) (by norm_num)
theorem B3465341 : Blo 1539967 3465341 := bbase (se 3 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 3465341 = 1299503) (by norm_num)
theorem B2310269 : Blo 1539967 2310269 := bbase (se 3 (by rfl) ⟨433175, by rfl⟩ : syracuseStep 2310269 = 866351) (by norm_num)
theorem B2310293 : Blo 1539967 2310293 := bbase (se 6 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 2310293 = 108295) (by norm_num)
theorem B2310317 : Blo 1539967 2310317 := bbase (se 3 (by rfl) ⟨433184, by rfl⟩ : syracuseStep 2310317 = 866369) (by norm_num)
theorem B3899573 : Blo 1539967 3899573 := bbase (se 5 (by rfl) ⟨182792, by rfl⟩ : syracuseStep 3899573 = 365585) (by norm_num)
theorem B8331445 : Blo 1539967 8331445 := bbase (se 5 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 8331445 = 781073) (by norm_num)
theorem B3465413 : Blo 1539967 3465413 := bbase (se 4 (by rfl) ⟨324882, by rfl⟩ : syracuseStep 3465413 = 649765) (by norm_num)
theorem B2310341 : Blo 1539967 2310341 := bbase (se 4 (by rfl) ⟨216594, by rfl⟩ : syracuseStep 2310341 = 433189) (by norm_num)
theorem B2924741 : Blo 1539967 2924741 := bbase (se 4 (by rfl) ⟨274194, by rfl⟩ : syracuseStep 2924741 = 548389) (by norm_num)
theorem B2310365 : Blo 1539967 2310365 := bbase (se 3 (by rfl) ⟨433193, by rfl⟩ : syracuseStep 2310365 = 866387) (by norm_num)
theorem B7028965 : Blo 1539967 7028965 := bbase (se 4 (by rfl) ⟨658965, by rfl⟩ : syracuseStep 7028965 = 1317931) (by norm_num)
theorem B1949933 : Blo 1539967 1949933 := bbase (se 3 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 1949933 = 731225) (by norm_num)
theorem B2310389 : Blo 1539967 2310389 := bbase (se 5 (by rfl) ⟨108299, by rfl⟩ : syracuseStep 2310389 = 216599) (by norm_num)
theorem B3465485 : Blo 1539967 3465485 := bbase (se 3 (by rfl) ⟨649778, by rfl⟩ : syracuseStep 3465485 = 1299557) (by norm_num)
theorem B2310413 : Blo 1539967 2310413 := bbase (se 3 (by rfl) ⟨433202, by rfl⟩ : syracuseStep 2310413 = 866405) (by norm_num)
theorem B5202197 : Blo 1539967 5202197 := bbase (se 6 (by rfl) ⟨121926, by rfl⟩ : syracuseStep 5202197 = 243853) (by norm_num)
theorem B2310437 : Blo 1539967 2310437 := bbase (se 4 (by rfl) ⟨216603, by rfl⟩ : syracuseStep 2310437 = 433207) (by norm_num)
theorem B1949989 : Blo 1539967 1949989 := bbase (se 4 (by rfl) ⟨182811, by rfl⟩ : syracuseStep 1949989 = 365623) (by norm_num)
theorem B2310461 : Blo 1539967 2310461 := bbase (se 3 (by rfl) ⟨433211, by rfl⟩ : syracuseStep 2310461 = 866423) (by norm_num)
theorem B4686149 : Blo 1539967 4686149 := bbase (se 4 (by rfl) ⟨439326, by rfl⟩ : syracuseStep 4686149 = 878653) (by norm_num)
theorem B3465557 : Blo 1539967 3465557 := bbase (se 10 (by rfl) ⟨5076, by rfl⟩ : syracuseStep 3465557 = 10153) (by norm_num)
theorem B2310485 : Blo 1539967 2310485 := bbase (se 10 (by rfl) ⟨3384, by rfl⟩ : syracuseStep 2310485 = 6769) (by norm_num)
theorem B2924885 : Blo 1539967 2924885 := bbase (se 10 (by rfl) ⟨4284, by rfl⟩ : syracuseStep 2924885 = 8569) (by norm_num)
theorem B2777437 : Blo 1539967 2777437 := bbase (se 3 (by rfl) ⟨520769, by rfl⟩ : syracuseStep 2777437 = 1041539) (by norm_num)
theorem B2310509 : Blo 1539967 2310509 := bbase (se 3 (by rfl) ⟨433220, by rfl⟩ : syracuseStep 2310509 = 866441) (by norm_num)
theorem B3899765 : Blo 1539967 3899765 := bbase (se 5 (by rfl) ⟨182801, by rfl⟩ : syracuseStep 3899765 = 365603) (by norm_num)
theorem B2310533 : Blo 1539967 2310533 := bbase (se 4 (by rfl) ⟨216612, by rfl⟩ : syracuseStep 2310533 = 433225) (by norm_num)
theorem B1950085 : Blo 1539967 1950085 := bbase (se 4 (by rfl) ⟨182820, by rfl⟩ : syracuseStep 1950085 = 365641) (by norm_num)
theorem B3514757 : Blo 1539967 3514757 := bbase (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) (by norm_num)
theorem B3465629 : Blo 1539967 3465629 := bbase (se 3 (by rfl) ⟨649805, by rfl⟩ : syracuseStep 3465629 = 1299611) (by norm_num)
theorem B2310557 : Blo 1539967 2310557 := bbase (se 3 (by rfl) ⟨433229, by rfl⟩ : syracuseStep 2310557 = 866459) (by norm_num)
theorem B1851817 : Blo 1539967 1851817 := bbase (se 2 (by rfl) ⟨694431, by rfl⟩ : syracuseStep 1851817 = 1388863) (by norm_num)
theorem B2310581 : Blo 1539967 2310581 := bbase (se 5 (by rfl) ⟨108308, by rfl⟩ : syracuseStep 2310581 = 216617) (by norm_num)
theorem B2310605 : Blo 1539967 2310605 := bbase (se 3 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 2310605 = 866477) (by norm_num)
theorem B3465701 : Blo 1539967 3465701 := bbase (se 4 (by rfl) ⟨324909, by rfl⟩ : syracuseStep 3465701 = 649819) (by norm_num)
theorem B2310629 : Blo 1539967 2310629 := bbase (se 4 (by rfl) ⟨216621, by rfl⟩ : syracuseStep 2310629 = 433243) (by norm_num)
theorem B2310653 : Blo 1539967 2310653 := bbase (se 3 (by rfl) ⟨433247, by rfl⟩ : syracuseStep 2310653 = 866495) (by norm_num)
theorem B2310677 : Blo 1539967 2310677 := bbase (se 6 (by rfl) ⟨54156, by rfl⟩ : syracuseStep 2310677 = 108313) (by norm_num)
theorem B3465773 : Blo 1539967 3465773 := bbase (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) (by norm_num)
theorem B2310701 : Blo 1539967 2310701 := bbase (se 3 (by rfl) ⟨433256, by rfl⟩ : syracuseStep 2310701 = 866513) (by norm_num)
theorem B1950257 : Blo 1539967 1950257 := bbase (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) (by norm_num)
theorem B2310725 : Blo 1539967 2310725 := bbase (se 4 (by rfl) ⟨216630, by rfl⟩ : syracuseStep 2310725 = 433261) (by norm_num)
theorem B2310749 : Blo 1539967 2310749 := bbase (se 3 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 2310749 = 866531) (by norm_num)
theorem B1950313 : Blo 1539967 1950313 := bbase (se 2 (by rfl) ⟨731367, by rfl⟩ : syracuseStep 1950313 = 1462735) (by norm_num)
theorem B3465845 : Blo 1539967 3465845 := bbase (se 5 (by rfl) ⟨162461, by rfl⟩ : syracuseStep 3465845 = 324923) (by norm_num)
theorem B2310773 : Blo 1539967 2310773 := bbase (se 5 (by rfl) ⟨108317, by rfl⟩ : syracuseStep 2310773 = 216635) (by norm_num)
theorem B2925173 : Blo 1539967 2925173 := bbase (se 5 (by rfl) ⟨137117, by rfl⟩ : syracuseStep 2925173 = 274235) (by norm_num)
theorem B2310797 : Blo 1539967 2310797 := bbase (se 3 (by rfl) ⟨433274, by rfl⟩ : syracuseStep 2310797 = 866549) (by norm_num)
theorem B2777741 : Blo 1539967 2777741 := bbase (se 3 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 2777741 = 1041653) (by norm_num)
theorem B2310821 : Blo 1539967 2310821 := bbase (se 4 (by rfl) ⟨216639, by rfl⟩ : syracuseStep 2310821 = 433279) (by norm_num)
theorem B3465917 : Blo 1539967 3465917 := bbase (se 3 (by rfl) ⟨649859, by rfl⟩ : syracuseStep 3465917 = 1299719) (by norm_num)
theorem B2310845 : Blo 1539967 2310845 := bbase (se 3 (by rfl) ⟨433283, by rfl⟩ : syracuseStep 2310845 = 866567) (by norm_num)
theorem B1950409 : Blo 1539967 1950409 := bbase (se 2 (by rfl) ⟨731403, by rfl⟩ : syracuseStep 1950409 = 1462807) (by norm_num)
theorem B3900109 : Blo 1539967 3900109 := bbase (se 3 (by rfl) ⟨731270, by rfl⟩ : syracuseStep 3900109 = 1462541) (by norm_num)
theorem B2310869 : Blo 1539967 2310869 := bbase (se 7 (by rfl) ⟨27080, by rfl⟩ : syracuseStep 2310869 = 54161) (by norm_num)
theorem B2851549 : Blo 1539967 2851549 := bbase (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) (by norm_num)
theorem B2310893 : Blo 1539967 2310893 := bbase (se 3 (by rfl) ⟨433292, by rfl⟩ : syracuseStep 2310893 = 866585) (by norm_num)
theorem B3465989 : Blo 1539967 3465989 := bbase (se 4 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 3465989 = 649873) (by norm_num)
theorem B2310917 : Blo 1539967 2310917 := bbase (se 4 (by rfl) ⟨216648, by rfl⟩ : syracuseStep 2310917 = 433297) (by norm_num)
theorem B2925325 : Blo 1539967 2925325 := bbase (se 3 (by rfl) ⟨548498, by rfl⟩ : syracuseStep 2925325 = 1096997) (by norm_num)
theorem B2310941 : Blo 1539967 2310941 := bbase (se 3 (by rfl) ⟨433301, by rfl⟩ : syracuseStep 2310941 = 866603) (by norm_num)
theorem B2310965 : Blo 1539967 2310965 := bbase (se 5 (by rfl) ⟨108326, by rfl⟩ : syracuseStep 2310965 = 216653) (by norm_num)
theorem B3900221 : Blo 1539967 3900221 := bbase (se 3 (by rfl) ⟨731291, by rfl⟩ : syracuseStep 3900221 = 1462583) (by norm_num)
theorem B3466061 : Blo 1539967 3466061 := bbase (se 3 (by rfl) ⟨649886, by rfl⟩ : syracuseStep 3466061 = 1299773) (by norm_num)
theorem B2310989 : Blo 1539967 2310989 := bbase (se 3 (by rfl) ⟨433310, by rfl⟩ : syracuseStep 2310989 = 866621) (by norm_num)
theorem B2311013 : Blo 1539967 2311013 := bbase (se 4 (by rfl) ⟨216657, by rfl⟩ : syracuseStep 2311013 = 433315) (by norm_num)
theorem B1950581 : Blo 1539967 1950581 := bbase (se 5 (by rfl) ⟨91433, by rfl⟩ : syracuseStep 1950581 = 182867) (by norm_num)
theorem B2311037 : Blo 1539967 2311037 := bbase (se 3 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 2311037 = 866639) (by norm_num)
theorem B3466133 : Blo 1539967 3466133 := bbase (se 6 (by rfl) ⟨81237, by rfl⟩ : syracuseStep 3466133 = 162475) (by norm_num)
theorem B2311061 : Blo 1539967 2311061 := bbase (se 6 (by rfl) ⟨54165, by rfl⟩ : syracuseStep 2311061 = 108331) (by norm_num)
theorem B2311085 : Blo 1539967 2311085 := bbase (se 3 (by rfl) ⟨433328, by rfl⟩ : syracuseStep 2311085 = 866657) (by norm_num)
theorem B1950637 : Blo 1539967 1950637 := bbase (se 3 (by rfl) ⟨365744, by rfl⟩ : syracuseStep 1950637 = 731489) (by norm_num)
theorem B2311109 : Blo 1539967 2311109 := bbase (se 4 (by rfl) ⟨216666, by rfl⟩ : syracuseStep 2311109 = 433333) (by norm_num)
theorem B3466205 : Blo 1539967 3466205 := bbase (se 3 (by rfl) ⟨649913, by rfl⟩ : syracuseStep 3466205 = 1299827) (by norm_num)
theorem B2311133 : Blo 1539967 2311133 := bbase (se 3 (by rfl) ⟨433337, by rfl⟩ : syracuseStep 2311133 = 866675) (by norm_num)
theorem B2311157 : Blo 1539967 2311157 := bbase (se 5 (by rfl) ⟨108335, by rfl⟩ : syracuseStep 2311157 = 216671) (by norm_num)
theorem B3900413 : Blo 1539967 3900413 := bbase (se 3 (by rfl) ⟨731327, by rfl⟩ : syracuseStep 3900413 = 1462655) (by norm_num)
theorem B7799813 : Blo 1539967 7799813 := bbase (se 4 (by rfl) ⟨731232, by rfl⟩ : syracuseStep 7799813 = 1462465) (by norm_num)
theorem B2311181 : Blo 1539967 2311181 := bbase (se 3 (by rfl) ⟨433346, by rfl⟩ : syracuseStep 2311181 = 866693) (by norm_num)
theorem B1950733 : Blo 1539967 1950733 := bbase (se 3 (by rfl) ⟨365762, by rfl⟩ : syracuseStep 1950733 = 731525) (by norm_num)
theorem B3466277 : Blo 1539967 3466277 := bbase (se 4 (by rfl) ⟨324963, by rfl⟩ : syracuseStep 3466277 = 649927) (by norm_num)
theorem B2311205 : Blo 1539967 2311205 := bbase (se 4 (by rfl) ⟨216675, by rfl⟩ : syracuseStep 2311205 = 433351) (by norm_num)
theorem B2311229 : Blo 1539967 2311229 := bbase (se 3 (by rfl) ⟨433355, by rfl⟩ : syracuseStep 2311229 = 866711) (by norm_num)
theorem B2925629 : Blo 1539967 2925629 := bbase (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) (by norm_num)
theorem B2311253 : Blo 1539967 2311253 := bbase (se 8 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 2311253 = 27085) (by norm_num)
theorem B3466349 : Blo 1539967 3466349 := bbase (se 3 (by rfl) ⟨649940, by rfl⟩ : syracuseStep 3466349 = 1299881) (by norm_num)
theorem B2311277 : Blo 1539967 2311277 := bbase (se 3 (by rfl) ⟨433364, by rfl⟩ : syracuseStep 2311277 = 866729) (by norm_num)
theorem B2311301 : Blo 1539967 2311301 := bbase (se 4 (by rfl) ⟨216684, by rfl⟩ : syracuseStep 2311301 = 433369) (by norm_num)
theorem B2311325 : Blo 1539967 2311325 := bbase (se 3 (by rfl) ⟨433373, by rfl⟩ : syracuseStep 2311325 = 866747) (by norm_num)
theorem B2081965 : Blo 1539967 2081965 := bbase (se 3 (by rfl) ⟨390368, by rfl⟩ : syracuseStep 2081965 = 780737) (by norm_num)
theorem B3466421 : Blo 1539967 3466421 := bbase (se 5 (by rfl) ⟨162488, by rfl⟩ : syracuseStep 3466421 = 324977) (by norm_num)
theorem B8774837 : Blo 1539967 8774837 := bbase (se 5 (by rfl) ⟨411320, by rfl⟩ : syracuseStep 8774837 = 822641) (by norm_num)
theorem B2311349 : Blo 1539967 2311349 := bbase (se 5 (by rfl) ⟨108344, by rfl⟩ : syracuseStep 2311349 = 216689) (by norm_num)
theorem B1950905 : Blo 1539967 1950905 := bbase (se 2 (by rfl) ⟨731589, by rfl⟩ : syracuseStep 1950905 = 1463179) (by norm_num)
theorem B2311373 : Blo 1539967 2311373 := bbase (se 3 (by rfl) ⟨433382, by rfl⟩ : syracuseStep 2311373 = 866765) (by norm_num)
theorem B2311397 : Blo 1539967 2311397 := bbase (se 4 (by rfl) ⟨216693, by rfl⟩ : syracuseStep 2311397 = 433387) (by norm_num)
theorem B3466493 : Blo 1539967 3466493 := bbase (se 3 (by rfl) ⟨649967, by rfl⟩ : syracuseStep 3466493 = 1299935) (by norm_num)
theorem B2311421 : Blo 1539967 2311421 := bbase (se 3 (by rfl) ⟨433391, by rfl⟩ : syracuseStep 2311421 = 866783) (by norm_num)
theorem B11699477 : Blo 1539967 11699477 := bbase (se 6 (by rfl) ⟨274206, by rfl⟩ : syracuseStep 11699477 = 548413) (by norm_num)
theorem B2311445 : Blo 1539967 2311445 := bbase (se 6 (by rfl) ⟨54174, by rfl⟩ : syracuseStep 2311445 = 108349) (by norm_num)
theorem B2311469 : Blo 1539967 2311469 := bbase (se 3 (by rfl) ⟨433400, by rfl⟩ : syracuseStep 2311469 = 866801) (by norm_num)
theorem B2467141 : Blo 1539967 2467141 := bbase (se 4 (by rfl) ⟨231294, by rfl⟩ : syracuseStep 2467141 = 462589) (by norm_num)
theorem B3466565 : Blo 1539967 3466565 := bbase (se 4 (by rfl) ⟨324990, by rfl⟩ : syracuseStep 3466565 = 649981) (by norm_num)
theorem B2311493 : Blo 1539967 2311493 := bbase (se 4 (by rfl) ⟨216702, by rfl⟩ : syracuseStep 2311493 = 433405) (by norm_num)
theorem B3900757 : Blo 1539967 3900757 := bbase (se 12 (by rfl) ⟨1428, by rfl⟩ : syracuseStep 3900757 = 2857) (by norm_num)
theorem B2311517 : Blo 1539967 2311517 := bbase (se 3 (by rfl) ⟨433409, by rfl⟩ : syracuseStep 2311517 = 866819) (by norm_num)
theorem B2311541 : Blo 1539967 2311541 := bbase (se 5 (by rfl) ⟨108353, by rfl⟩ : syracuseStep 2311541 = 216707) (by norm_num)
theorem B3466637 : Blo 1539967 3466637 := bbase (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) (by norm_num)
theorem B2311565 : Blo 1539967 2311565 := bbase (se 3 (by rfl) ⟨433418, by rfl⟩ : syracuseStep 2311565 = 866837) (by norm_num)
theorem B2311589 : Blo 1539967 2311589 := bbase (se 4 (by rfl) ⟨216711, by rfl⟩ : syracuseStep 2311589 = 433423) (by norm_num)
theorem B2311613 : Blo 1539967 2311613 := bbase (se 3 (by rfl) ⟨433427, by rfl⟩ : syracuseStep 2311613 = 866855) (by norm_num)
theorem B3900869 : Blo 1539967 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B3466709 : Blo 1539967 3466709 := bbase (se 7 (by rfl) ⟨40625, by rfl⟩ : syracuseStep 3466709 = 81251) (by norm_num)
theorem B2311637 : Blo 1539967 2311637 := bbase (se 7 (by rfl) ⟨27089, by rfl⟩ : syracuseStep 2311637 = 54179) (by norm_num)
theorem B4007405 : Blo 1539967 4007405 := bbase (se 3 (by rfl) ⟨751388, by rfl⟩ : syracuseStep 4007405 = 1502777) (by norm_num)
theorem B2311661 : Blo 1539967 2311661 := bbase (se 3 (by rfl) ⟨433436, by rfl⟩ : syracuseStep 2311661 = 866873) (by norm_num)
theorem B2311685 : Blo 1539967 2311685 := bbase (se 4 (by rfl) ⟨216720, by rfl⟩ : syracuseStep 2311685 = 433441) (by norm_num)
theorem B3466781 : Blo 1539967 3466781 := bbase (se 3 (by rfl) ⟨650021, by rfl⟩ : syracuseStep 3466781 = 1300043) (by norm_num)
theorem B2311709 : Blo 1539967 2311709 := bbase (se 3 (by rfl) ⟨433445, by rfl⟩ : syracuseStep 2311709 = 866891) (by norm_num)
theorem B1975861 : Blo 1539967 1975861 := bbase (se 5 (by rfl) ⟨92618, by rfl⟩ : syracuseStep 1975861 = 185237) (by norm_num)
theorem B2311733 : Blo 1539967 2311733 := bbase (se 5 (by rfl) ⟨108362, by rfl⟩ : syracuseStep 2311733 = 216725) (by norm_num)
theorem B2311757 : Blo 1539967 2311757 := bbase (se 3 (by rfl) ⟨433454, by rfl⟩ : syracuseStep 2311757 = 866909) (by norm_num)
theorem B3466853 : Blo 1539967 3466853 := bbase (se 4 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 3466853 = 650035) (by norm_num)
theorem B2311781 : Blo 1539967 2311781 := bbase (se 4 (by rfl) ⟨216729, by rfl⟩ : syracuseStep 2311781 = 433459) (by norm_num)
theorem B3335789 : Blo 1539967 3335789 := bbase (se 3 (by rfl) ⟨625460, by rfl⟩ : syracuseStep 3335789 = 1250921) (by norm_num)
theorem B2311805 : Blo 1539967 2311805 := bbase (se 3 (by rfl) ⟨433463, by rfl⟩ : syracuseStep 2311805 = 866927) (by norm_num)
theorem B3901061 : Blo 1539967 3901061 := bbase (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) (by norm_num)
theorem B2311829 : Blo 1539967 2311829 := bbase (se 6 (by rfl) ⟨54183, by rfl⟩ : syracuseStep 2311829 = 108367) (by norm_num)
theorem B3466925 : Blo 1539967 3466925 := bbase (se 3 (by rfl) ⟨650048, by rfl⟩ : syracuseStep 3466925 = 1300097) (by norm_num)
theorem B2311853 : Blo 1539967 2311853 := bbase (se 3 (by rfl) ⟨433472, by rfl⟩ : syracuseStep 2311853 = 866945) (by norm_num)
theorem B14050997 : Blo 1539967 14050997 := bbase (se 5 (by rfl) ⟨658640, by rfl⟩ : syracuseStep 14050997 = 1317281) (by norm_num)
theorem B2311877 : Blo 1539967 2311877 := bbase (se 4 (by rfl) ⟨216738, by rfl⟩ : syracuseStep 2311877 = 433477) (by norm_num)
theorem B14804693 : Blo 1539967 14804693 := bbase (se 7 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 14804693 = 346985) (by norm_num)
theorem B2311901 : Blo 1539967 2311901 := bbase (se 3 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 2311901 = 866963) (by norm_num)
theorem B3466997 : Blo 1539967 3466997 := bbase (se 5 (by rfl) ⟨162515, by rfl⟩ : syracuseStep 3466997 = 325031) (by norm_num)
theorem B2311925 : Blo 1539967 2311925 := bbase (se 5 (by rfl) ⟨108371, by rfl⟩ : syracuseStep 2311925 = 216743) (by norm_num)
theorem B2467597 : Blo 1539967 2467597 := bbase (se 3 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 2467597 = 925349) (by norm_num)
theorem B2311949 : Blo 1539967 2311949 := bbase (se 3 (by rfl) ⟨433490, by rfl⟩ : syracuseStep 2311949 = 866981) (by norm_num)
theorem B2311973 : Blo 1539967 2311973 := bbase (se 4 (by rfl) ⟨216747, by rfl⟩ : syracuseStep 2311973 = 433495) (by norm_num)
theorem B2926381 : Blo 1539967 2926381 := bbase (se 3 (by rfl) ⟨548696, by rfl⟩ : syracuseStep 2926381 = 1097393) (by norm_num)
theorem B2598709 : Blo 1539967 2598709 := bbase (se 5 (by rfl) ⟨121814, by rfl⟩ : syracuseStep 2598709 = 243629) (by norm_num)
theorem B3467069 : Blo 1539967 3467069 := bbase (se 3 (by rfl) ⟨650075, by rfl⟩ : syracuseStep 3467069 = 1300151) (by norm_num)
theorem B2311997 : Blo 1539967 2311997 := bbase (se 3 (by rfl) ⟨433499, by rfl⟩ : syracuseStep 2311997 = 866999) (by norm_num)
theorem B2312021 : Blo 1539967 2312021 := bbase (se 9 (by rfl) ⟨6773, by rfl⟩ : syracuseStep 2312021 = 13547) (by norm_num)
theorem B2312045 : Blo 1539967 2312045 := bbase (se 3 (by rfl) ⟨433508, by rfl⟩ : syracuseStep 2312045 = 867017) (by norm_num)
theorem B3467141 : Blo 1539967 3467141 := bbase (se 4 (by rfl) ⟨325044, by rfl⟩ : syracuseStep 3467141 = 650089) (by norm_num)
theorem B2312069 : Blo 1539967 2312069 := bbase (se 4 (by rfl) ⟨216756, by rfl⟩ : syracuseStep 2312069 = 433513) (by norm_num)
theorem B2598797 : Blo 1539967 2598797 := bbase (se 3 (by rfl) ⟨487274, by rfl⟩ : syracuseStep 2598797 = 974549) (by norm_num)
theorem B2312093 : Blo 1539967 2312093 := bbase (se 3 (by rfl) ⟨433517, by rfl⟩ : syracuseStep 2312093 = 867035) (by norm_num)
theorem B3123125 : Blo 1539967 3123125 := bbase (se 5 (by rfl) ⟨146396, by rfl⟩ : syracuseStep 3123125 = 292793) (by norm_num)
theorem B5851061 : Blo 1539967 5851061 := bbase (se 5 (by rfl) ⟨274268, by rfl⟩ : syracuseStep 5851061 = 548537) (by norm_num)
theorem B2312117 : Blo 1539967 2312117 := bbase (se 5 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 2312117 = 216761) (by norm_num)
theorem B3467213 : Blo 1539967 3467213 := bbase (se 3 (by rfl) ⟨650102, by rfl⟩ : syracuseStep 3467213 = 1300205) (by norm_num)
theorem B2312141 : Blo 1539967 2312141 := bbase (se 3 (by rfl) ⟨433526, by rfl⟩ : syracuseStep 2312141 = 867053) (by norm_num)
theorem B3901405 : Blo 1539967 3901405 := bbase (se 3 (by rfl) ⟨731513, by rfl⟩ : syracuseStep 3901405 = 1463027) (by norm_num)
theorem B2312165 : Blo 1539967 2312165 := bbase (se 4 (by rfl) ⟨216765, by rfl⟩ : syracuseStep 2312165 = 433531) (by norm_num)
theorem B2312189 : Blo 1539967 2312189 := bbase (se 3 (by rfl) ⟨433535, by rfl⟩ : syracuseStep 2312189 = 867071) (by norm_num)
theorem B2598925 : Blo 1539967 2598925 := bbase (se 3 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 2598925 = 974597) (by norm_num)
theorem B3467285 : Blo 1539967 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B3901517 : Blo 1539967 3901517 := bbase (se 3 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 3901517 = 1463069) (by norm_num)
theorem B3467357 : Blo 1539967 3467357 := bbase (se 3 (by rfl) ⟨650129, by rfl⟩ : syracuseStep 3467357 = 1300259) (by norm_num)
theorem B2599013 : Blo 1539967 2599013 := bbase (se 4 (by rfl) ⟨243657, by rfl⟩ : syracuseStep 2599013 = 487315) (by norm_num)
theorem B1927325 : Blo 1539967 1927325 := bbase (se 3 (by rfl) ⟨361373, by rfl⟩ : syracuseStep 1927325 = 722747) (by norm_num)
theorem B3467429 : Blo 1539967 3467429 := bbase (se 4 (by rfl) ⟨325071, by rfl⟩ : syracuseStep 3467429 = 650143) (by norm_num)
theorem B5851349 : Blo 1539967 5851349 := bbase (se 7 (by rfl) ⟨68570, by rfl⟩ : syracuseStep 5851349 = 137141) (by norm_num)
theorem B2599141 : Blo 1539967 2599141 := bbase (se 4 (by rfl) ⟨243669, by rfl⟩ : syracuseStep 2599141 = 487339) (by norm_num)
theorem B3467501 : Blo 1539967 3467501 := bbase (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) (by norm_num)
theorem B3901709 : Blo 1539967 3901709 := bbase (se 3 (by rfl) ⟨731570, by rfl⟩ : syracuseStep 3901709 = 1463141) (by norm_num)
theorem B7801109 : Blo 1539967 7801109 := bbase (se 6 (by rfl) ⟨182838, by rfl⟩ : syracuseStep 7801109 = 365677) (by norm_num)
theorem B3467573 : Blo 1539967 3467573 := bbase (se 5 (by rfl) ⟨162542, by rfl⟩ : syracuseStep 3467573 = 325085) (by norm_num)
theorem B2599229 : Blo 1539967 2599229 := bbase (se 3 (by rfl) ⟨487355, by rfl⟩ : syracuseStep 2599229 = 974711) (by norm_num)
theorem B3467645 : Blo 1539967 3467645 := bbase (se 3 (by rfl) ⟨650183, by rfl⟩ : syracuseStep 3467645 = 1300367) (by norm_num)
theorem B2468269 : Blo 1539967 2468269 := bbase (se 3 (by rfl) ⟨462800, by rfl⟩ : syracuseStep 2468269 = 925601) (by norm_num)
theorem B2599357 : Blo 1539967 2599357 := bbase (se 3 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 2599357 = 974759) (by norm_num)
theorem B3467717 : Blo 1539967 3467717 := bbase (se 4 (by rfl) ⟨325098, by rfl⟩ : syracuseStep 3467717 = 650197) (by norm_num)
theorem B3467789 : Blo 1539967 3467789 := bbase (se 3 (by rfl) ⟨650210, by rfl⟩ : syracuseStep 3467789 = 1300421) (by norm_num)
theorem B2599445 : Blo 1539967 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B3467861 : Blo 1539967 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B2599573 : Blo 1539967 2599573 := bbase (se 6 (by rfl) ⟨60927, by rfl⟩ : syracuseStep 2599573 = 121855) (by norm_num)
theorem B3467933 : Blo 1539967 3467933 := bbase (se 3 (by rfl) ⟨650237, by rfl⟩ : syracuseStep 3467933 = 1300475) (by norm_num)
theorem B3468005 : Blo 1539967 3468005 := bbase (se 4 (by rfl) ⟨325125, by rfl⟩ : syracuseStep 3468005 = 650251) (by norm_num)
theorem B2599661 : Blo 1539967 2599661 := bbase (se 3 (by rfl) ⟨487436, by rfl⟩ : syracuseStep 2599661 = 974873) (by norm_num)
theorem B4385573 : Blo 1539967 4385573 := bbase (se 4 (by rfl) ⟨411147, by rfl⟩ : syracuseStep 4385573 = 822295) (by norm_num)
theorem B3468077 : Blo 1539967 3468077 := bbase (se 3 (by rfl) ⟨650264, by rfl⟩ : syracuseStep 3468077 = 1300529) (by norm_num)
theorem B2468693 : Blo 1539967 2468693 := bbase (se 9 (by rfl) ⟨7232, by rfl⟩ : syracuseStep 2468693 = 14465) (by norm_num)
theorem B2599789 : Blo 1539967 2599789 := bbase (se 3 (by rfl) ⟨487460, by rfl⟩ : syracuseStep 2599789 = 974921) (by norm_num)
theorem B3468149 : Blo 1539967 3468149 := bbase (se 5 (by rfl) ⟨162569, by rfl⟩ : syracuseStep 3468149 = 325139) (by norm_num)
theorem B3951517 : Blo 1539967 3951517 := bbase (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) (by norm_num)
theorem B3468221 : Blo 1539967 3468221 := bbase (se 3 (by rfl) ⟨650291, by rfl⟩ : syracuseStep 3468221 = 1300583) (by norm_num)
theorem B2599877 : Blo 1539967 2599877 := bbase (se 4 (by rfl) ⟨243738, by rfl⟩ : syracuseStep 2599877 = 487477) (by norm_num)
theorem B3468293 : Blo 1539967 3468293 := bbase (se 4 (by rfl) ⟨325152, by rfl⟩ : syracuseStep 3468293 = 650305) (by norm_num)
theorem B3124261 : Blo 1539967 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B7400501 : Blo 1539967 7400501 := bbase (se 5 (by rfl) ⟨346898, by rfl⟩ : syracuseStep 7400501 = 693797) (by norm_num)
theorem B2600005 : Blo 1539967 2600005 := bbase (se 4 (by rfl) ⟨243750, by rfl⟩ : syracuseStep 2600005 = 487501) (by norm_num)
theorem B2468981 : Blo 1539967 2468981 := bbase (se 5 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 2468981 = 231467) (by norm_num)
theorem B2600093 : Blo 1539967 2600093 := bbase (se 3 (by rfl) ⟨487517, by rfl⟩ : syracuseStep 2600093 = 975035) (by norm_num)
theorem B2600221 : Blo 1539967 2600221 := bbase (se 3 (by rfl) ⟨487541, by rfl⟩ : syracuseStep 2600221 = 975083) (by norm_num)
theorem B6581573 : Blo 1539967 6581573 := bbase (se 4 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 6581573 = 1234045) (by norm_num)
theorem B2223445 : Blo 1539967 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B2600309 : Blo 1539967 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B5852533 : Blo 1539967 5852533 := bbase (se 5 (by rfl) ⟨274337, by rfl⟩ : syracuseStep 5852533 = 548675) (by norm_num)
theorem B6245765 : Blo 1539967 6245765 := bbase (se 4 (by rfl) ⟨585540, by rfl⟩ : syracuseStep 6245765 = 1171081) (by norm_num)
theorem B2600437 : Blo 1539967 2600437 := bbase (se 5 (by rfl) ⟨121895, by rfl⟩ : syracuseStep 2600437 = 243791) (by norm_num)
theorem B4386325 : Blo 1539967 4386325 := bbase (se 6 (by rfl) ⟨102804, by rfl⟩ : syracuseStep 4386325 = 205609) (by norm_num)
theorem B4935205 : Blo 1539967 4935205 := bbase (se 4 (by rfl) ⟨462675, by rfl⟩ : syracuseStep 4935205 = 925351) (by norm_num)
theorem B7802405 : Blo 1539967 7802405 := bbase (se 4 (by rfl) ⟨731475, by rfl⟩ : syracuseStep 7802405 = 1462951) (by norm_num)
theorem B2600525 : Blo 1539967 2600525 := bbase (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) (by norm_num)
theorem B5197445 : Blo 1539967 5197445 := bbase (se 4 (by rfl) ⟨487260, by rfl⟩ : syracuseStep 5197445 = 974521) (by norm_num)
theorem B1805981 : Blo 1539967 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B3165869 : Blo 1539967 3165869 := bbase (se 3 (by rfl) ⟨593600, by rfl⟩ : syracuseStep 3165869 = 1187201) (by norm_num)
theorem B9875125 : Blo 1539967 9875125 := bbase (se 5 (by rfl) ⟨462896, by rfl⟩ : syracuseStep 9875125 = 925793) (by norm_num)
theorem B2600653 : Blo 1539967 2600653 := bbase (se 3 (by rfl) ⟨487622, by rfl⟩ : syracuseStep 2600653 = 975245) (by norm_num)
theorem B9367285 : Blo 1539967 9367285 := bbase (se 5 (by rfl) ⟨439091, by rfl⟩ : syracuseStep 9367285 = 878183) (by norm_num)
theorem B1756937 : Blo 1539967 1756937 := bbase (se 2 (by rfl) ⟨658851, by rfl⟩ : syracuseStep 1756937 = 1317703) (by norm_num)
theorem B7401253 : Blo 1539967 7401253 := bbase (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) (by norm_num)
theorem B2600741 : Blo 1539967 2600741 := bbase (se 4 (by rfl) ⟨243819, by rfl⟩ : syracuseStep 2600741 = 487639) (by norm_num)
theorem B1732477 : Blo 1539967 1732477 := bbase (se 3 (by rfl) ⟨324839, by rfl⟩ : syracuseStep 1732477 = 649679) (by norm_num)
theorem B1732513 : Blo 1539967 1732513 := bbase (se 2 (by rfl) ⟨649692, by rfl⟩ : syracuseStep 1732513 = 1299385) (by norm_num)
theorem B2600869 : Blo 1539967 2600869 := bbase (se 4 (by rfl) ⟨243831, by rfl⟩ : syracuseStep 2600869 = 487663) (by norm_num)
theorem B1732549 : Blo 1539967 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B3289061 : Blo 1539967 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B1732585 : Blo 1539967 1732585 := bbase (se 2 (by rfl) ⟨649719, by rfl⟩ : syracuseStep 1732585 = 1299439) (by norm_num)
theorem B2600957 : Blo 1539967 2600957 := bbase (se 3 (by rfl) ⟨487679, by rfl⟩ : syracuseStep 2600957 = 975359) (by norm_num)
theorem B1732621 : Blo 1539967 1732621 := bbase (se 3 (by rfl) ⟨324866, by rfl⟩ : syracuseStep 1732621 = 649733) (by norm_num)
theorem B1732657 : Blo 1539967 1732657 := bbase (se 2 (by rfl) ⟨649746, by rfl⟩ : syracuseStep 1732657 = 1299493) (by norm_num)
theorem B5197877 : Blo 1539967 5197877 := bbase (se 5 (by rfl) ⟨243650, by rfl⟩ : syracuseStep 5197877 = 487301) (by norm_num)
theorem B1732693 : Blo 1539967 1732693 := bbase (se 8 (by rfl) ⟨10152, by rfl⟩ : syracuseStep 1732693 = 20305) (by norm_num)
theorem B1732729 : Blo 1539967 1732729 := bbase (se 2 (by rfl) ⟨649773, by rfl⟩ : syracuseStep 1732729 = 1299547) (by norm_num)
theorem B2601085 : Blo 1539967 2601085 := bbase (se 3 (by rfl) ⟨487703, by rfl⟩ : syracuseStep 2601085 = 975407) (by norm_num)
theorem B1732765 : Blo 1539967 1732765 := bbase (se 3 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 1732765 = 649787) (by norm_num)
theorem B1732801 : Blo 1539967 1732801 := bbase (se 2 (by rfl) ⟨649800, by rfl⟩ : syracuseStep 1732801 = 1299601) (by norm_num)
theorem B2601173 : Blo 1539967 2601173 := bbase (se 7 (by rfl) ⟨30482, by rfl⟩ : syracuseStep 2601173 = 60965) (by norm_num)
theorem B1732837 : Blo 1539967 1732837 := bbase (se 4 (by rfl) ⟨162453, by rfl⟩ : syracuseStep 1732837 = 324907) (by norm_num)
theorem B1732873 : Blo 1539967 1732873 := bbase (se 2 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 1732873 = 1299655) (by norm_num)
theorem B1732909 : Blo 1539967 1732909 := bbase (se 3 (by rfl) ⟨324920, by rfl⟩ : syracuseStep 1732909 = 649841) (by norm_num)
theorem B1732945 : Blo 1539967 1732945 := bbase (se 2 (by rfl) ⟨649854, by rfl⟩ : syracuseStep 1732945 = 1299709) (by norm_num)
theorem B1732981 : Blo 1539967 1732981 := bbase (se 5 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 1732981 = 162467) (by norm_num)
theorem B4166005 : Blo 1539967 4166005 := bbase (se 5 (by rfl) ⟨195281, by rfl⟩ : syracuseStep 4166005 = 390563) (by norm_num)
theorem B1733017 : Blo 1539967 1733017 := bbase (se 2 (by rfl) ⟨649881, by rfl⟩ : syracuseStep 1733017 = 1299763) (by norm_num)
theorem B1733053 : Blo 1539967 1733053 := bbase (se 3 (by rfl) ⟨324947, by rfl⟩ : syracuseStep 1733053 = 649895) (by norm_num)
theorem B1733089 : Blo 1539967 1733089 := bbase (se 2 (by rfl) ⟨649908, by rfl⟩ : syracuseStep 1733089 = 1299817) (by norm_num)
theorem B5198309 : Blo 1539967 5198309 := bbase (se 4 (by rfl) ⟨487341, by rfl⟩ : syracuseStep 5198309 = 974683) (by norm_num)
theorem B6509045 : Blo 1539967 6509045 := bbase (se 5 (by rfl) ⟨305111, by rfl⟩ : syracuseStep 6509045 = 610223) (by norm_num)
theorem B1733125 : Blo 1539967 1733125 := bbase (se 4 (by rfl) ⟨162480, by rfl⟩ : syracuseStep 1733125 = 324961) (by norm_num)
theorem B11104789 : Blo 1539967 11104789 := bbase (se 6 (by rfl) ⟨260268, by rfl⟩ : syracuseStep 11104789 = 520537) (by norm_num)
theorem B12497429 : Blo 1539967 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B1733161 : Blo 1539967 1733161 := bbase (se 2 (by rfl) ⟨649935, by rfl⟩ : syracuseStep 1733161 = 1299871) (by norm_num)
theorem B1561141 : Blo 1539967 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B1733197 : Blo 1539967 1733197 := bbase (se 3 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 1733197 = 649949) (by norm_num)
theorem B3289693 : Blo 1539967 3289693 := bbase (se 3 (by rfl) ⟨616817, by rfl⟩ : syracuseStep 3289693 = 1233635) (by norm_num)
theorem B1733233 : Blo 1539967 1733233 := bbase (se 2 (by rfl) ⟨649962, by rfl⟩ : syracuseStep 1733233 = 1299925) (by norm_num)
theorem B5550709 : Blo 1539967 5550709 := bbase (se 5 (by rfl) ⟨260189, by rfl⟩ : syracuseStep 5550709 = 520379) (by norm_num)
theorem B1733269 : Blo 1539967 1733269 := bbase (se 6 (by rfl) ⟨40623, by rfl⟩ : syracuseStep 1733269 = 81247) (by norm_num)
theorem B1733305 : Blo 1539967 1733305 := bbase (se 2 (by rfl) ⟨649989, by rfl⟩ : syracuseStep 1733305 = 1299979) (by norm_num)
theorem B1733341 : Blo 1539967 1733341 := bbase (se 3 (by rfl) ⟨325001, by rfl⟩ : syracuseStep 1733341 = 650003) (by norm_num)
theorem B1733377 : Blo 1539967 1733377 := bbase (se 2 (by rfl) ⟨650016, by rfl⟩ : syracuseStep 1733377 = 1300033) (by norm_num)
theorem B5550869 : Blo 1539967 5550869 := bbase (se 6 (by rfl) ⟨130098, by rfl⟩ : syracuseStep 5550869 = 260197) (by norm_num)
theorem B1733413 : Blo 1539967 1733413 := bbase (se 4 (by rfl) ⟨162507, by rfl⟩ : syracuseStep 1733413 = 325015) (by norm_num)
theorem B1733449 : Blo 1539967 1733449 := bbase (se 2 (by rfl) ⟨650043, by rfl⟩ : syracuseStep 1733449 = 1300087) (by norm_num)
theorem B1733485 : Blo 1539967 1733485 := bbase (se 3 (by rfl) ⟨325028, by rfl⟩ : syracuseStep 1733485 = 650057) (by norm_num)
theorem B4936565 : Blo 1539967 4936565 := bbase (se 5 (by rfl) ⟨231401, by rfl⟩ : syracuseStep 4936565 = 462803) (by norm_num)
theorem B1733521 : Blo 1539967 1733521 := bbase (se 2 (by rfl) ⟨650070, by rfl⟩ : syracuseStep 1733521 = 1300141) (by norm_num)
theorem B5198741 : Blo 1539967 5198741 := bbase (se 6 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 5198741 = 243691) (by norm_num)
theorem B1733557 : Blo 1539967 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B1733593 : Blo 1539967 1733593 := bbase (se 2 (by rfl) ⟨650097, by rfl⟩ : syracuseStep 1733593 = 1300195) (by norm_num)
theorem B1733629 : Blo 1539967 1733629 := bbase (se 3 (by rfl) ⟨325055, by rfl⟩ : syracuseStep 1733629 = 650111) (by norm_num)
theorem B1733665 : Blo 1539967 1733665 := bbase (se 2 (by rfl) ⟨650124, by rfl⟩ : syracuseStep 1733665 = 1300249) (by norm_num)
theorem B7025717 : Blo 1539967 7025717 := bbase (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) (by norm_num)
theorem B6583349 : Blo 1539967 6583349 := bbase (se 5 (by rfl) ⟨308594, by rfl⟩ : syracuseStep 6583349 = 617189) (by norm_num)
theorem B1733701 : Blo 1539967 1733701 := bbase (se 4 (by rfl) ⟨162534, by rfl⟩ : syracuseStep 1733701 = 325069) (by norm_num)
theorem B1733737 : Blo 1539967 1733737 := bbase (se 2 (by rfl) ⟨650151, by rfl⟩ : syracuseStep 1733737 = 1300303) (by norm_num)
theorem B1733773 : Blo 1539967 1733773 := bbase (se 3 (by rfl) ⟨325082, by rfl⟩ : syracuseStep 1733773 = 650165) (by norm_num)
theorem B1733809 : Blo 1539967 1733809 := bbase (se 2 (by rfl) ⟨650178, by rfl⟩ : syracuseStep 1733809 = 1300357) (by norm_num)
theorem B1733845 : Blo 1539967 1733845 := bbase (se 7 (by rfl) ⟨20318, by rfl⟩ : syracuseStep 1733845 = 40637) (by norm_num)
theorem B1733881 : Blo 1539967 1733881 := bbase (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) (by norm_num)
theorem B1733917 : Blo 1539967 1733917 := bbase (se 3 (by rfl) ⟨325109, by rfl⟩ : syracuseStep 1733917 = 650219) (by norm_num)
theorem B6583589 : Blo 1539967 6583589 := bbase (se 4 (by rfl) ⟨617211, by rfl⟩ : syracuseStep 6583589 = 1234423) (by norm_num)
theorem B1733953 : Blo 1539967 1733953 := bbase (se 2 (by rfl) ⟨650232, by rfl⟩ : syracuseStep 1733953 = 1300465) (by norm_num)
theorem B5199173 : Blo 1539967 5199173 := bbase (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) (by norm_num)
theorem B1733989 : Blo 1539967 1733989 := bbase (se 4 (by rfl) ⟨162561, by rfl⟩ : syracuseStep 1733989 = 325123) (by norm_num)
theorem B1734025 : Blo 1539967 1734025 := bbase (se 2 (by rfl) ⟨650259, by rfl⟩ : syracuseStep 1734025 = 1300519) (by norm_num)
theorem B1734061 : Blo 1539967 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B1734097 : Blo 1539967 1734097 := bbase (se 2 (by rfl) ⟨650286, by rfl⟩ : syracuseStep 1734097 = 1300573) (by norm_num)
theorem B3290581 : Blo 1539967 3290581 := bbase (se 7 (by rfl) ⟨38561, by rfl⟩ : syracuseStep 3290581 = 77123) (by norm_num)
theorem B6247925 : Blo 1539967 6247925 := bbase (se 5 (by rfl) ⟨292871, by rfl⟩ : syracuseStep 6247925 = 585743) (by norm_num)
theorem B1734133 : Blo 1539967 1734133 := bbase (se 5 (by rfl) ⟨81287, by rfl⟩ : syracuseStep 1734133 = 162575) (by norm_num)
theorem B26318357 : Blo 1539967 26318357 := bbase (se 6 (by rfl) ⟨616836, by rfl⟩ : syracuseStep 26318357 = 1233673) (by norm_num)
theorem B3290701 : Blo 1539967 3290701 := bbase (se 3 (by rfl) ⟨617006, by rfl⟩ : syracuseStep 3290701 = 1234013) (by norm_num)
theorem B3700397 : Blo 1539967 3700397 := bbase (se 3 (by rfl) ⟨693824, by rfl⟩ : syracuseStep 3700397 = 1387649) (by norm_num)
theorem B5199605 : Blo 1539967 5199605 := bbase (se 5 (by rfl) ⟨243731, by rfl⟩ : syracuseStep 5199605 = 487463) (by norm_num)
theorem B3954421 : Blo 1539967 3954421 := bbase (se 5 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 3954421 = 370727) (by norm_num)
theorem B3290957 : Blo 1539967 3290957 := bbase (se 3 (by rfl) ⟨617054, by rfl⟩ : syracuseStep 3290957 = 1234109) (by norm_num)
theorem B6330325 : Blo 1539967 6330325 := bbase (se 7 (by rfl) ⟨74183, by rfl⟩ : syracuseStep 6330325 = 148367) (by norm_num)
theorem B3700781 : Blo 1539967 3700781 := bbase (se 3 (by rfl) ⟨693896, by rfl⟩ : syracuseStep 3700781 = 1387793) (by norm_num)
theorem B15005749 : Blo 1539967 15005749 := bbase (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) (by norm_num)
theorem B2193493 : Blo 1539967 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B5847173 : Blo 1539967 5847173 := bbase (se 4 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 5847173 = 1096345) (by norm_num)
theorem B5200037 : Blo 1539967 5200037 := bbase (se 4 (by rfl) ⟨487503, by rfl⟩ : syracuseStep 5200037 = 975007) (by norm_num)
theorem B3700981 : Blo 1539967 3700981 := bbase (se 5 (by rfl) ⟨173483, by rfl⟩ : syracuseStep 3700981 = 346967) (by norm_num)
theorem B3512605 : Blo 1539967 3512605 := bbase (se 3 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 3512605 = 1317227) (by norm_num)
theorem B1644829 : Blo 1539967 1644829 := bbase (se 3 (by rfl) ⟨308405, by rfl⟩ : syracuseStep 1644829 = 616811) (by norm_num)
theorem B4389173 : Blo 1539967 4389173 := bbase (se 5 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 4389173 = 411485) (by norm_num)
theorem B2029933 : Blo 1539967 2029933 := bbase (se 3 (by rfl) ⟨380612, by rfl⟩ : syracuseStep 2029933 = 761225) (by norm_num)
theorem B1644949 : Blo 1539967 1644949 := bbase (se 6 (by rfl) ⟨38553, by rfl⟩ : syracuseStep 1644949 = 77107) (by norm_num)
theorem B5847461 : Blo 1539967 5847461 := bbase (se 4 (by rfl) ⟨548199, by rfl⟩ : syracuseStep 5847461 = 1096399) (by norm_num)
theorem B26442197 : Blo 1539967 26442197 := bbase (se 7 (by rfl) ⟨309869, by rfl⟩ : syracuseStep 26442197 = 619739) (by norm_num)
theorem B7797221 : Blo 1539967 7797221 := bbase (se 4 (by rfl) ⟨730989, by rfl⟩ : syracuseStep 7797221 = 1461979) (by norm_num)
theorem B5200469 : Blo 1539967 5200469 := bbase (se 8 (by rfl) ⟨30471, by rfl⟩ : syracuseStep 5200469 = 60943) (by norm_num)
theorem B2341469 : Blo 1539967 2341469 := bbase (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) (by norm_num)
theorem B1645201 : Blo 1539967 1645201 := bbase (se 2 (by rfl) ⟨616950, by rfl⟩ : syracuseStep 1645201 = 1233901) (by norm_num)
theorem B1645205 : Blo 1539967 1645205 := bbase (se 6 (by rfl) ⟨38559, by rfl⟩ : syracuseStep 1645205 = 77119) (by norm_num)
theorem B2194085 : Blo 1539967 2194085 := bbase (se 4 (by rfl) ⟨205695, by rfl⟩ : syracuseStep 2194085 = 411391) (by norm_num)
theorem B3291845 : Blo 1539967 3291845 := bbase (se 4 (by rfl) ⟨308610, by rfl⟩ : syracuseStep 3291845 = 617221) (by norm_num)
theorem B2194165 : Blo 1539967 2194165 := bbase (se 5 (by rfl) ⟨102851, by rfl⟩ : syracuseStep 2194165 = 205703) (by norm_num)
theorem B6249221 : Blo 1539967 6249221 := bbase (se 4 (by rfl) ⟨585864, by rfl⟩ : syracuseStep 6249221 = 1171729) (by norm_num)
theorem B3898165 : Blo 1539967 3898165 := bbase (se 5 (by rfl) ⟨182726, by rfl⟩ : syracuseStep 3898165 = 365453) (by norm_num)
theorem B2030393 : Blo 1539967 2030393 := bbase (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) (by norm_num)
theorem B21379925 : Blo 1539967 21379925 := bbase (se 9 (by rfl) ⟨62636, by rfl⟩ : syracuseStep 21379925 = 125273) (by norm_num)
theorem B4750181 : Blo 1539967 4750181 := bbase (se 4 (by rfl) ⟨445329, by rfl⟩ : syracuseStep 4750181 = 890659) (by norm_num)
theorem B2194285 : Blo 1539967 2194285 := bbase (se 3 (by rfl) ⟨411428, by rfl⟩ : syracuseStep 2194285 = 822857) (by norm_num)
theorem B5553029 : Blo 1539967 5553029 := bbase (se 4 (by rfl) ⟨520596, by rfl⟩ : syracuseStep 5553029 = 1041193) (by norm_num)
theorem B3898277 : Blo 1539967 3898277 := bbase (se 4 (by rfl) ⟨365463, by rfl⟩ : syracuseStep 3898277 = 730927) (by norm_num)
theorem B3292085 : Blo 1539967 3292085 := bbase (se 5 (by rfl) ⟨154316, by rfl⟩ : syracuseStep 3292085 = 308633) (by norm_num)
theorem B2194381 : Blo 1539967 2194381 := bbase (se 3 (by rfl) ⟨411446, by rfl⟩ : syracuseStep 2194381 = 822893) (by norm_num)
theorem B5200901 : Blo 1539967 5200901 := bbase (se 4 (by rfl) ⟨487584, by rfl⟩ : syracuseStep 5200901 = 975169) (by norm_num)
theorem B4062221 : Blo 1539967 4062221 := bbase (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) (by norm_num)
theorem B3898469 : Blo 1539967 3898469 := bbase (se 4 (by rfl) ⟨365481, by rfl⟩ : syracuseStep 3898469 = 730963) (by norm_num)
theorem B4447349 : Blo 1539967 4447349 := bbase (se 5 (by rfl) ⟨208469, by rfl⟩ : syracuseStep 4447349 = 416939) (by norm_num)
theorem B2923685 : Blo 1539967 2923685 := bbase (se 4 (by rfl) ⟨274095, by rfl⟩ : syracuseStep 2923685 = 548191) (by norm_num)
theorem B5553317 : Blo 1539967 5553317 := bbase (se 4 (by rfl) ⟨520623, by rfl⟩ : syracuseStep 5553317 = 1041247) (by norm_num)
theorem B4447429 : Blo 1539967 4447429 := bbase (se 4 (by rfl) ⟨416946, by rfl⟩ : syracuseStep 4447429 = 833893) (by norm_num)
theorem B1645769 : Blo 1539967 1645769 := bbase (se 2 (by rfl) ⟨617163, by rfl⟩ : syracuseStep 1645769 = 1234327) (by norm_num)
theorem B1645957 : Blo 1539967 1645957 := bbase (se 4 (by rfl) ⟨154308, by rfl⟩ : syracuseStep 1645957 = 308617) (by norm_num)
theorem B1850789 : Blo 1539967 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B3513773 : Blo 1539967 3513773 := bbase (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) (by norm_num)
theorem B5201333 : Blo 1539967 5201333 := bbase (se 5 (by rfl) ⟨243812, by rfl⟩ : syracuseStep 5201333 = 487625) (by norm_num)
theorem B1949113 : Blo 1539967 1949113 := bbase (se 2 (by rfl) ⟨730917, by rfl⟩ : syracuseStep 1949113 = 1461835) (by norm_num)
theorem B3898813 : Blo 1539967 3898813 := bbase (se 3 (by rfl) ⟨731027, by rfl⟩ : syracuseStep 3898813 = 1462055) (by norm_num)
theorem B2965021 : Blo 1539967 2965021 := bbase (se 3 (by rfl) ⟨555941, by rfl⟩ : syracuseStep 2965021 = 1111883) (by norm_num)
theorem B3898925 : Blo 1539967 3898925 := bbase (se 3 (by rfl) ⟨731048, by rfl⟩ : syracuseStep 3898925 = 1462097) (by norm_num)
theorem B5848645 : Blo 1539967 5848645 := bbase (se 4 (by rfl) ⟨548310, by rfl⟩ : syracuseStep 5848645 = 1096621) (by norm_num)
theorem B1949285 : Blo 1539967 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B1949341 : Blo 1539967 1949341 := bbase (se 3 (by rfl) ⟨365501, by rfl⟩ : syracuseStep 1949341 = 731003) (by norm_num)
theorem B3899117 : Blo 1539967 3899117 := bbase (se 3 (by rfl) ⟨731084, by rfl⟩ : syracuseStep 3899117 = 1462169) (by norm_num)
theorem B1851121 : Blo 1539967 1851121 := bbase (se 2 (by rfl) ⟨694170, by rfl⟩ : syracuseStep 1851121 = 1388341) (by norm_num)
theorem B7798517 : Blo 1539967 7798517 := bbase (se 5 (by rfl) ⟨365555, by rfl⟩ : syracuseStep 7798517 = 731111) (by norm_num)
theorem B1949437 : Blo 1539967 1949437 := bbase (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) (by norm_num)
theorem B3464981 : Blo 1539967 3464981 := bbase (se 6 (by rfl) ⟨81210, by rfl⟩ : syracuseStep 3464981 = 162421) (by norm_num)
theorem B17547029 : Blo 1539967 17547029 := bbase (se 6 (by rfl) ⟨411258, by rfl⟩ : syracuseStep 17547029 = 822517) (by norm_num)
theorem B3702557 : Blo 1539967 3702557 := bbase (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) (by norm_num)
theorem B2309957 : Blo 1539967 2309957 := bbase (se 4 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 2309957 = 433117) (by norm_num)
theorem B2309981 : Blo 1539967 2309981 := bbase (se 3 (by rfl) ⟨433121, by rfl⟩ : syracuseStep 2309981 = 866243) (by norm_num)
theorem B3465053 : Blo 1539967 3465053 := bbase (se 3 (by rfl) ⟨649697, by rfl⟩ : syracuseStep 3465053 = 1299395) (by norm_num)
theorem B5201765 : Blo 1539967 5201765 := bbase (se 4 (by rfl) ⟨487665, by rfl⟩ : syracuseStep 5201765 = 975331) (by norm_num)
theorem B2310005 : Blo 1539967 2310005 := bbase (se 5 (by rfl) ⟨108281, by rfl⟩ : syracuseStep 2310005 = 216563) (by norm_num)
theorem B5848949 : Blo 1539967 5848949 := bbase (se 5 (by rfl) ⟨274169, by rfl⟩ : syracuseStep 5848949 = 548339) (by norm_num)
theorem B2310029 : Blo 1539967 2310029 := bbase (se 3 (by rfl) ⟨433130, by rfl⟩ : syracuseStep 2310029 = 866261) (by norm_num)
theorem B2924437 : Blo 1539967 2924437 := bbase (se 6 (by rfl) ⟨68541, by rfl⟩ : syracuseStep 2924437 = 137083) (by norm_num)
theorem B2310053 : Blo 1539967 2310053 := bbase (se 4 (by rfl) ⟨216567, by rfl⟩ : syracuseStep 2310053 = 433135) (by norm_num)
theorem B3465125 : Blo 1539967 3465125 := bbase (se 4 (by rfl) ⟨324855, by rfl⟩ : syracuseStep 3465125 = 649711) (by norm_num)
theorem B1949609 : Blo 1539967 1949609 := bbase (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) (by norm_num)
theorem B2310077 : Blo 1539967 2310077 := bbase (se 3 (by rfl) ⟨433139, by rfl⟩ : syracuseStep 2310077 = 866279) (by norm_num)
theorem B2310101 : Blo 1539967 2310101 := bbase (se 7 (by rfl) ⟨27071, by rfl⟩ : syracuseStep 2310101 = 54143) (by norm_num)
theorem B1949665 : Blo 1539967 1949665 := bbase (se 2 (by rfl) ⟨731124, by rfl⟩ : syracuseStep 1949665 = 1462249) (by norm_num)
theorem B2310125 : Blo 1539967 2310125 := bbase (se 3 (by rfl) ⟨433148, by rfl⟩ : syracuseStep 2310125 = 866297) (by norm_num)
theorem B3465197 : Blo 1539967 3465197 := bbase (se 3 (by rfl) ⟨649724, by rfl⟩ : syracuseStep 3465197 = 1299449) (by norm_num)
theorem B1540099 : Blo 1539967 1540099 := bstep (se 1 (by rfl) ⟨1155074, by rfl⟩ : syracuseStep 1540099 = 2310149) B2310149
theorem B3465233 : Blo 1539967 3465233 := bstep (se 2 (by rfl) ⟨1299462, by rfl⟩ : syracuseStep 3465233 = 2598925) B2598925
theorem B2310161 : Blo 1539967 2310161 := bstep (se 2 (by rfl) ⟨866310, by rfl⟩ : syracuseStep 2310161 = 1732621) B1732621
theorem B1540115 : Blo 1539967 1540115 := bstep (se 1 (by rfl) ⟨1155086, by rfl⟩ : syracuseStep 1540115 = 2310173) B2310173
theorem B3465251 : Blo 1539967 3465251 := bstep (se 1 (by rfl) ⟨2598938, by rfl⟩ : syracuseStep 3465251 = 5197877) B5197877
theorem B2310179 : Blo 1539967 2310179 := bstep (se 1 (by rfl) ⟨1732634, by rfl⟩ : syracuseStep 2310179 = 3465269) B3465269
theorem B1540131 : Blo 1539967 1540131 := bstep (se 1 (by rfl) ⟨1155098, by rfl⟩ : syracuseStep 1540131 = 2310197) B2310197
theorem B3899441 : Blo 1539967 3899441 := bstep (se 2 (by rfl) ⟨1462290, by rfl⟩ : syracuseStep 3899441 = 2924581) B2924581
theorem B1540147 : Blo 1539967 1540147 := bstep (se 1 (by rfl) ⟨1155110, by rfl⟩ : syracuseStep 1540147 = 2310221) B2310221
theorem B2310209 : Blo 1539967 2310209 := bstep (se 2 (by rfl) ⟨866328, by rfl⟩ : syracuseStep 2310209 = 1732657) B1732657
theorem B1540163 : Blo 1539967 1540163 := bstep (se 1 (by rfl) ⟨1155122, by rfl⟩ : syracuseStep 1540163 = 2310245) B2310245
theorem B2310227 : Blo 1539967 2310227 := bstep (se 1 (by rfl) ⟨1732670, by rfl⟩ : syracuseStep 2310227 = 3465341) B3465341
theorem B1540179 : Blo 1539967 1540179 := bstep (se 1 (by rfl) ⟨1155134, by rfl⟩ : syracuseStep 1540179 = 2310269) B2310269
theorem B1540195 : Blo 1539967 1540195 := bstep (se 1 (by rfl) ⟨1155146, by rfl⟩ : syracuseStep 1540195 = 2310293) B2310293
theorem B2310257 : Blo 1539967 2310257 := bstep (se 2 (by rfl) ⟨866346, by rfl⟩ : syracuseStep 2310257 = 1732693) B1732693
theorem B2924657 : Blo 1539967 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1540211 : Blo 1539967 1540211 := bstep (se 1 (by rfl) ⟨1155158, by rfl⟩ : syracuseStep 1540211 = 2310317) B2310317
theorem B2310275 : Blo 1539967 2310275 := bstep (se 1 (by rfl) ⟨1732706, by rfl⟩ : syracuseStep 2310275 = 3465413) B3465413
theorem B1540227 : Blo 1539967 1540227 := bstep (se 1 (by rfl) ⟨1155170, by rfl⟩ : syracuseStep 1540227 = 2310341) B2310341
theorem B1949827 : Blo 1539967 1949827 := bstep (se 1 (by rfl) ⟨1462370, by rfl⟩ : syracuseStep 1949827 = 2924741) B2924741
theorem B18735245 : Blo 1539967 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B1540243 : Blo 1539967 1540243 := bstep (se 1 (by rfl) ⟨1155182, by rfl⟩ : syracuseStep 1540243 = 2310365) B2310365
theorem B2310305 : Blo 1539967 2310305 := bstep (se 2 (by rfl) ⟨866364, by rfl⟩ : syracuseStep 2310305 = 1732729) B1732729
theorem B1540259 : Blo 1539967 1540259 := bstep (se 1 (by rfl) ⟨1155194, by rfl⟩ : syracuseStep 1540259 = 2310389) B2310389
theorem B2310323 : Blo 1539967 2310323 := bstep (se 1 (by rfl) ⟨1732742, by rfl⟩ : syracuseStep 2310323 = 3465485) B3465485
theorem B1540275 : Blo 1539967 1540275 := bstep (se 1 (by rfl) ⟨1155206, by rfl⟩ : syracuseStep 1540275 = 2310413) B2310413
theorem B1540291 : Blo 1539967 1540291 := bstep (se 1 (by rfl) ⟨1155218, by rfl⟩ : syracuseStep 1540291 = 2310437) B2310437
theorem B2310353 : Blo 1539967 2310353 := bstep (se 2 (by rfl) ⟨866382, by rfl⟩ : syracuseStep 2310353 = 1732765) B1732765
theorem B1540307 : Blo 1539967 1540307 := bstep (se 1 (by rfl) ⟨1155230, by rfl⟩ : syracuseStep 1540307 = 2310461) B2310461
theorem B2310371 : Blo 1539967 2310371 := bstep (se 1 (by rfl) ⟨1732778, by rfl⟩ : syracuseStep 2310371 = 3465557) B3465557
theorem B1540323 : Blo 1539967 1540323 := bstep (se 1 (by rfl) ⟨1155242, by rfl⟩ : syracuseStep 1540323 = 2310485) B2310485
theorem B1949923 : Blo 1539967 1949923 := bstep (se 1 (by rfl) ⟨1462442, by rfl⟩ : syracuseStep 1949923 = 2924885) B2924885
theorem B11108593 : Blo 1539967 11108593 := bstep (se 2 (by rfl) ⟨4165722, by rfl⟩ : syracuseStep 11108593 = 8331445) B8331445
theorem B1540339 : Blo 1539967 1540339 := bstep (se 1 (by rfl) ⟨1155254, by rfl⟩ : syracuseStep 1540339 = 2310509) B2310509
theorem B2310401 : Blo 1539967 2310401 := bstep (se 2 (by rfl) ⟨866400, by rfl⟩ : syracuseStep 2310401 = 1732801) B1732801
theorem B1540355 : Blo 1539967 1540355 := bstep (se 1 (by rfl) ⟨1155266, by rfl⟩ : syracuseStep 1540355 = 2310533) B2310533
theorem B2310419 : Blo 1539967 2310419 := bstep (se 1 (by rfl) ⟨1732814, by rfl⟩ : syracuseStep 2310419 = 3465629) B3465629
theorem B1540371 : Blo 1539967 1540371 := bstep (se 1 (by rfl) ⟨1155278, by rfl⟩ : syracuseStep 1540371 = 2310557) B2310557
theorem B1540387 : Blo 1539967 1540387 := bstep (se 1 (by rfl) ⟨1155290, by rfl⟩ : syracuseStep 1540387 = 2310581) B2310581
theorem B3465521 : Blo 1539967 3465521 := bstep (se 2 (by rfl) ⟨1299570, by rfl⟩ : syracuseStep 3465521 = 2599141) B2599141
theorem B2310449 : Blo 1539967 2310449 := bstep (se 2 (by rfl) ⟨866418, by rfl⟩ : syracuseStep 2310449 = 1732837) B1732837
theorem B1540403 : Blo 1539967 1540403 := bstep (se 1 (by rfl) ⟨1155302, by rfl⟩ : syracuseStep 1540403 = 2310605) B2310605
theorem B9371953 : Blo 1539967 9371953 := bstep (se 2 (by rfl) ⟨3514482, by rfl⟩ : syracuseStep 9371953 = 7028965) B7028965
theorem B3465539 : Blo 1539967 3465539 := bstep (se 1 (by rfl) ⟨2599154, by rfl⟩ : syracuseStep 3465539 = 5198309) B5198309
theorem B2310467 : Blo 1539967 2310467 := bstep (se 1 (by rfl) ⟨1732850, by rfl⟩ : syracuseStep 2310467 = 3465701) B3465701
theorem B1540419 : Blo 1539967 1540419 := bstep (se 1 (by rfl) ⟨1155314, by rfl⟩ : syracuseStep 1540419 = 2310629) B2310629
theorem B1540435 : Blo 1539967 1540435 := bstep (se 1 (by rfl) ⟨1155326, by rfl⟩ : syracuseStep 1540435 = 2310653) B2310653
theorem B2310497 : Blo 1539967 2310497 := bstep (se 2 (by rfl) ⟨866436, by rfl⟩ : syracuseStep 2310497 = 1732873) B1732873
theorem B1540451 : Blo 1539967 1540451 := bstep (se 1 (by rfl) ⟨1155338, by rfl⟩ : syracuseStep 1540451 = 2310677) B2310677
theorem B2310515 : Blo 1539967 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B1540467 : Blo 1539967 1540467 := bstep (se 1 (by rfl) ⟨1155350, by rfl⟩ : syracuseStep 1540467 = 2310701) B2310701
theorem B1540483 : Blo 1539967 1540483 := bstep (se 1 (by rfl) ⟨1155362, by rfl⟩ : syracuseStep 1540483 = 2310725) B2310725
theorem B2310545 : Blo 1539967 2310545 := bstep (se 2 (by rfl) ⟨866454, by rfl⟩ : syracuseStep 2310545 = 1732909) B1732909
theorem B1540499 : Blo 1539967 1540499 := bstep (se 1 (by rfl) ⟨1155374, by rfl⟩ : syracuseStep 1540499 = 2310749) B2310749
theorem B2310563 : Blo 1539967 2310563 := bstep (se 1 (by rfl) ⟨1732922, by rfl⟩ : syracuseStep 2310563 = 3465845) B3465845
theorem B1540515 : Blo 1539967 1540515 := bstep (se 1 (by rfl) ⟨1155386, by rfl⟩ : syracuseStep 1540515 = 2310773) B2310773
theorem B1540531 : Blo 1539967 1540531 := bstep (se 1 (by rfl) ⟨1155398, by rfl⟩ : syracuseStep 1540531 = 2310797) B2310797
theorem B1851827 : Blo 1539967 1851827 := bstep (se 1 (by rfl) ⟨1388870, by rfl⟩ : syracuseStep 1851827 = 2777741) B2777741
theorem B2310593 : Blo 1539967 2310593 := bstep (se 2 (by rfl) ⟨866472, by rfl⟩ : syracuseStep 2310593 = 1732945) B1732945
theorem B1540547 : Blo 1539967 1540547 := bstep (se 1 (by rfl) ⟨1155410, by rfl⟩ : syracuseStep 1540547 = 2310821) B2310821
theorem B3703249 : Blo 1539967 3703249 := bstep (se 2 (by rfl) ⟨1388718, by rfl⟩ : syracuseStep 3703249 = 2777437) B2777437
theorem B2310611 : Blo 1539967 2310611 := bstep (se 1 (by rfl) ⟨1732958, by rfl⟩ : syracuseStep 2310611 = 3465917) B3465917
theorem B1540563 : Blo 1539967 1540563 := bstep (se 1 (by rfl) ⟨1155422, by rfl⟩ : syracuseStep 1540563 = 2310845) B2310845
theorem B1540579 : Blo 1539967 1540579 := bstep (se 1 (by rfl) ⟨1155434, by rfl⟩ : syracuseStep 1540579 = 2310869) B2310869
theorem B5202413 : Blo 1539967 5202413 := bstep (se 3 (by rfl) ⟨975452, by rfl⟩ : syracuseStep 5202413 = 1950905) B1950905
theorem B2310641 : Blo 1539967 2310641 := bstep (se 2 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 2310641 = 1732981) B1732981
theorem B5554673 : Blo 1539967 5554673 := bstep (se 2 (by rfl) ⟨2083002, by rfl⟩ : syracuseStep 5554673 = 4166005) B4166005
theorem B1540595 : Blo 1539967 1540595 := bstep (se 1 (by rfl) ⟨1155446, by rfl⟩ : syracuseStep 1540595 = 2310893) B2310893
theorem B2310659 : Blo 1539967 2310659 := bstep (se 1 (by rfl) ⟨1732994, by rfl⟩ : syracuseStep 2310659 = 3465989) B3465989
theorem B1540611 : Blo 1539967 1540611 := bstep (se 1 (by rfl) ⟨1155458, by rfl⟩ : syracuseStep 1540611 = 2310917) B2310917
theorem B1540627 : Blo 1539967 1540627 := bstep (se 1 (by rfl) ⟨1155470, by rfl⟩ : syracuseStep 1540627 = 2310941) B2310941
theorem B2310689 : Blo 1539967 2310689 := bstep (se 2 (by rfl) ⟨866508, by rfl⟩ : syracuseStep 2310689 = 1733017) B1733017
theorem B1540643 : Blo 1539967 1540643 := bstep (se 1 (by rfl) ⟨1155482, by rfl⟩ : syracuseStep 1540643 = 2310965) B2310965
theorem B2310707 : Blo 1539967 2310707 := bstep (se 1 (by rfl) ⟨1733030, by rfl⟩ : syracuseStep 2310707 = 3466061) B3466061
theorem B1540659 : Blo 1539967 1540659 := bstep (se 1 (by rfl) ⟨1155494, by rfl⟩ : syracuseStep 1540659 = 2310989) B2310989
theorem B1540675 : Blo 1539967 1540675 := bstep (se 1 (by rfl) ⟨1155506, by rfl⟩ : syracuseStep 1540675 = 2311013) B2311013
theorem B3465809 : Blo 1539967 3465809 := bstep (se 2 (by rfl) ⟨1299678, by rfl⟩ : syracuseStep 3465809 = 2599357) B2599357
theorem B2310737 : Blo 1539967 2310737 := bstep (se 2 (by rfl) ⟨866526, by rfl⟩ : syracuseStep 2310737 = 1733053) B1733053
theorem B1540691 : Blo 1539967 1540691 := bstep (se 1 (by rfl) ⟨1155518, by rfl⟩ : syracuseStep 1540691 = 2311037) B2311037
theorem B3465827 : Blo 1539967 3465827 := bstep (se 1 (by rfl) ⟨2599370, by rfl⟩ : syracuseStep 3465827 = 5198741) B5198741
theorem B2310755 : Blo 1539967 2310755 := bstep (se 1 (by rfl) ⟨1733066, by rfl⟩ : syracuseStep 2310755 = 3466133) B3466133
theorem B1540707 : Blo 1539967 1540707 := bstep (se 1 (by rfl) ⟨1155530, by rfl⟩ : syracuseStep 1540707 = 2311061) B2311061
theorem B1540723 : Blo 1539967 1540723 := bstep (se 1 (by rfl) ⟨1155542, by rfl⟩ : syracuseStep 1540723 = 2311085) B2311085
theorem B2310785 : Blo 1539967 2310785 := bstep (se 2 (by rfl) ⟨866544, by rfl⟩ : syracuseStep 2310785 = 1733089) B1733089
theorem B1540739 : Blo 1539967 1540739 := bstep (se 1 (by rfl) ⟨1155554, by rfl⟩ : syracuseStep 1540739 = 2311109) B2311109
theorem B2310803 : Blo 1539967 2310803 := bstep (se 1 (by rfl) ⟨1733102, by rfl⟩ : syracuseStep 2310803 = 3466205) B3466205
theorem B1540755 : Blo 1539967 1540755 := bstep (se 1 (by rfl) ⟨1155566, by rfl⟩ : syracuseStep 1540755 = 2311133) B2311133
theorem B1540771 : Blo 1539967 1540771 := bstep (se 1 (by rfl) ⟨1155578, by rfl⟩ : syracuseStep 1540771 = 2311157) B2311157
theorem B2310833 : Blo 1539967 2310833 := bstep (se 2 (by rfl) ⟨866562, by rfl⟩ : syracuseStep 2310833 = 1733125) B1733125
theorem B1540787 : Blo 1539967 1540787 := bstep (se 1 (by rfl) ⟨1155590, by rfl⟩ : syracuseStep 1540787 = 2311181) B2311181
theorem B2310851 : Blo 1539967 2310851 := bstep (se 1 (by rfl) ⟨1733138, by rfl⟩ : syracuseStep 2310851 = 3466277) B3466277
theorem B1540803 : Blo 1539967 1540803 := bstep (se 1 (by rfl) ⟨1155602, by rfl⟩ : syracuseStep 1540803 = 2311205) B2311205
theorem B1540819 : Blo 1539967 1540819 := bstep (se 1 (by rfl) ⟨1155614, by rfl⟩ : syracuseStep 1540819 = 2311229) B2311229
theorem B1950419 : Blo 1539967 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B2310881 : Blo 1539967 2310881 := bstep (se 2 (by rfl) ⟨866580, by rfl⟩ : syracuseStep 2310881 = 1733161) B1733161
theorem B1540835 : Blo 1539967 1540835 := bstep (se 1 (by rfl) ⟨1155626, by rfl⟩ : syracuseStep 1540835 = 2311253) B2311253
theorem B2081521 : Blo 1539967 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B2310899 : Blo 1539967 2310899 := bstep (se 1 (by rfl) ⟨1733174, by rfl⟩ : syracuseStep 2310899 = 3466349) B3466349
theorem B1540851 : Blo 1539967 1540851 := bstep (se 1 (by rfl) ⟨1155638, by rfl⟩ : syracuseStep 1540851 = 2311277) B2311277
theorem B1540867 : Blo 1539967 1540867 := bstep (se 1 (by rfl) ⟨1155650, by rfl⟩ : syracuseStep 1540867 = 2311301) B2311301
theorem B8774405 : Blo 1539967 8774405 := bstep (se 4 (by rfl) ⟨822600, by rfl⟩ : syracuseStep 8774405 = 1645201) B1645201
theorem B2310929 : Blo 1539967 2310929 := bstep (se 2 (by rfl) ⟨866598, by rfl⟩ : syracuseStep 2310929 = 1733197) B1733197
theorem B1540883 : Blo 1539967 1540883 := bstep (se 1 (by rfl) ⟨1155662, by rfl⟩ : syracuseStep 1540883 = 2311325) B2311325
theorem B2310947 : Blo 1539967 2310947 := bstep (se 1 (by rfl) ⟨1733210, by rfl⟩ : syracuseStep 2310947 = 3466421) B3466421
theorem B5849891 : Blo 1539967 5849891 := bstep (se 1 (by rfl) ⟨4387418, by rfl⟩ : syracuseStep 5849891 = 8774837) B8774837
theorem B1540899 : Blo 1539967 1540899 := bstep (se 1 (by rfl) ⟨1155674, by rfl⟩ : syracuseStep 1540899 = 2311349) B2311349
theorem B1540915 : Blo 1539967 1540915 := bstep (se 1 (by rfl) ⟨1155686, by rfl⟩ : syracuseStep 1540915 = 2311373) B2311373
theorem B2310977 : Blo 1539967 2310977 := bstep (se 2 (by rfl) ⟨866616, by rfl⟩ : syracuseStep 2310977 = 1733233) B1733233
theorem B1540931 : Blo 1539967 1540931 := bstep (se 1 (by rfl) ⟨1155698, by rfl⟩ : syracuseStep 1540931 = 2311397) B2311397
theorem B2310995 : Blo 1539967 2310995 := bstep (se 1 (by rfl) ⟨1733246, by rfl⟩ : syracuseStep 2310995 = 3466493) B3466493
theorem B1540947 : Blo 1539967 1540947 := bstep (se 1 (by rfl) ⟨1155710, by rfl⟩ : syracuseStep 1540947 = 2311421) B2311421
theorem B7799651 : Blo 1539967 7799651 := bstep (se 1 (by rfl) ⟨5849738, by rfl⟩ : syracuseStep 7799651 = 11699477) B11699477
theorem B1540963 : Blo 1539967 1540963 := bstep (se 1 (by rfl) ⟨1155722, by rfl⟩ : syracuseStep 1540963 = 2311445) B2311445
theorem B3466097 : Blo 1539967 3466097 := bstep (se 2 (by rfl) ⟨1299786, by rfl⟩ : syracuseStep 3466097 = 2599573) B2599573
theorem B2311025 : Blo 1539967 2311025 := bstep (se 2 (by rfl) ⟨866634, by rfl⟩ : syracuseStep 2311025 = 1733269) B1733269
theorem B1540979 : Blo 1539967 1540979 := bstep (se 1 (by rfl) ⟨1155734, by rfl⟩ : syracuseStep 1540979 = 2311469) B2311469
theorem B3466115 : Blo 1539967 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B2311043 : Blo 1539967 2311043 := bstep (se 1 (by rfl) ⟨1733282, by rfl⟩ : syracuseStep 2311043 = 3466565) B3466565
theorem B1540995 : Blo 1539967 1540995 := bstep (se 1 (by rfl) ⟨1155746, by rfl⟩ : syracuseStep 1540995 = 2311493) B2311493
theorem B1541011 : Blo 1539967 1541011 := bstep (se 1 (by rfl) ⟨1155758, by rfl⟩ : syracuseStep 1541011 = 2311517) B2311517
theorem B2311073 : Blo 1539967 2311073 := bstep (se 2 (by rfl) ⟨866652, by rfl⟩ : syracuseStep 2311073 = 1733305) B1733305
theorem B1541027 : Blo 1539967 1541027 := bstep (se 1 (by rfl) ⟨1155770, by rfl⟩ : syracuseStep 1541027 = 2311541) B2311541
theorem B2311091 : Blo 1539967 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B1541043 : Blo 1539967 1541043 := bstep (se 1 (by rfl) ⟨1155782, by rfl⟩ : syracuseStep 1541043 = 2311565) B2311565
theorem B1541059 : Blo 1539967 1541059 := bstep (se 1 (by rfl) ⟨1155794, by rfl⟩ : syracuseStep 1541059 = 2311589) B2311589
theorem B2311121 : Blo 1539967 2311121 := bstep (se 2 (by rfl) ⟨866670, by rfl⟩ : syracuseStep 2311121 = 1733341) B1733341
theorem B1541075 : Blo 1539967 1541075 := bstep (se 1 (by rfl) ⟨1155806, by rfl⟩ : syracuseStep 1541075 = 2311613) B2311613
theorem B2311139 : Blo 1539967 2311139 := bstep (se 1 (by rfl) ⟨1733354, by rfl⟩ : syracuseStep 2311139 = 3466709) B3466709
theorem B1541091 : Blo 1539967 1541091 := bstep (se 1 (by rfl) ⟨1155818, by rfl⟩ : syracuseStep 1541091 = 2311637) B2311637
theorem B2925553 : Blo 1539967 2925553 := bstep (se 2 (by rfl) ⟨1097082, by rfl⟩ : syracuseStep 2925553 = 2194165) B2194165
theorem B2671603 : Blo 1539967 2671603 := bstep (se 1 (by rfl) ⟨2003702, by rfl⟩ : syracuseStep 2671603 = 4007405) B4007405
theorem B1541107 : Blo 1539967 1541107 := bstep (se 1 (by rfl) ⟨1155830, by rfl⟩ : syracuseStep 1541107 = 2311661) B2311661
theorem B2311169 : Blo 1539967 2311169 := bstep (se 2 (by rfl) ⟨866688, by rfl⟩ : syracuseStep 2311169 = 1733377) B1733377
theorem B1541123 : Blo 1539967 1541123 := bstep (se 1 (by rfl) ⟨1155842, by rfl⟩ : syracuseStep 1541123 = 2311685) B2311685
theorem B9372685 : Blo 1539967 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B3900433 : Blo 1539967 3900433 := bstep (se 2 (by rfl) ⟨1462662, by rfl⟩ : syracuseStep 3900433 = 2925325) B2925325
theorem B2311187 : Blo 1539967 2311187 := bstep (se 1 (by rfl) ⟨1733390, by rfl⟩ : syracuseStep 2311187 = 3466781) B3466781
theorem B1541139 : Blo 1539967 1541139 := bstep (se 1 (by rfl) ⟨1155854, by rfl⟩ : syracuseStep 1541139 = 2311709) B2311709
theorem B1541155 : Blo 1539967 1541155 := bstep (se 1 (by rfl) ⟨1155866, by rfl⟩ : syracuseStep 1541155 = 2311733) B2311733
theorem B2311217 : Blo 1539967 2311217 := bstep (se 2 (by rfl) ⟨866706, by rfl⟩ : syracuseStep 2311217 = 1733413) B1733413
theorem B1541171 : Blo 1539967 1541171 := bstep (se 1 (by rfl) ⟨1155878, by rfl⟩ : syracuseStep 1541171 = 2311757) B2311757
theorem B2311235 : Blo 1539967 2311235 := bstep (se 1 (by rfl) ⟨1733426, by rfl⟩ : syracuseStep 2311235 = 3466853) B3466853
theorem B1541187 : Blo 1539967 1541187 := bstep (se 1 (by rfl) ⟨1155890, by rfl⟩ : syracuseStep 1541187 = 2311781) B2311781
theorem B1541203 : Blo 1539967 1541203 := bstep (se 1 (by rfl) ⟨1155902, by rfl⟩ : syracuseStep 1541203 = 2311805) B2311805
theorem B2311265 : Blo 1539967 2311265 := bstep (se 2 (by rfl) ⟨866724, by rfl⟩ : syracuseStep 2311265 = 1733449) B1733449
theorem B1541219 : Blo 1539967 1541219 := bstep (se 1 (by rfl) ⟨1155914, by rfl⟩ : syracuseStep 1541219 = 2311829) B2311829
theorem B2466931 : Blo 1539967 2466931 := bstep (se 1 (by rfl) ⟨1850198, by rfl⟩ : syracuseStep 2466931 = 3700397) B3700397
theorem B2311283 : Blo 1539967 2311283 := bstep (se 1 (by rfl) ⟨1733462, by rfl⟩ : syracuseStep 2311283 = 3466925) B3466925
theorem B1541235 : Blo 1539967 1541235 := bstep (se 1 (by rfl) ⟨1155926, by rfl⟩ : syracuseStep 1541235 = 2311853) B2311853
theorem B1541251 : Blo 1539967 1541251 := bstep (se 1 (by rfl) ⟨1155938, by rfl⟩ : syracuseStep 1541251 = 2311877) B2311877
theorem B3466385 : Blo 1539967 3466385 := bstep (se 2 (by rfl) ⟨1299894, by rfl⟩ : syracuseStep 3466385 = 2599789) B2599789
theorem B2311313 : Blo 1539967 2311313 := bstep (se 2 (by rfl) ⟨866742, by rfl⟩ : syracuseStep 2311313 = 1733485) B1733485
theorem B2925713 : Blo 1539967 2925713 := bstep (se 2 (by rfl) ⟨1097142, by rfl⟩ : syracuseStep 2925713 = 2194285) B2194285
theorem B1541267 : Blo 1539967 1541267 := bstep (se 1 (by rfl) ⟨1155950, by rfl⟩ : syracuseStep 1541267 = 2311901) B2311901
theorem B3466403 : Blo 1539967 3466403 := bstep (se 1 (by rfl) ⟨2599802, by rfl⟩ : syracuseStep 3466403 = 5199605) B5199605
theorem B2311331 : Blo 1539967 2311331 := bstep (se 1 (by rfl) ⟨1733498, by rfl⟩ : syracuseStep 2311331 = 3466997) B3466997
theorem B1541283 : Blo 1539967 1541283 := bstep (se 1 (by rfl) ⟨1155962, by rfl⟩ : syracuseStep 1541283 = 2311925) B2311925
theorem B1541299 : Blo 1539967 1541299 := bstep (se 1 (by rfl) ⟨1155974, by rfl⟩ : syracuseStep 1541299 = 2311949) B2311949
theorem B2311361 : Blo 1539967 2311361 := bstep (se 2 (by rfl) ⟨866760, by rfl⟩ : syracuseStep 2311361 = 1733521) B1733521
theorem B1541315 : Blo 1539967 1541315 := bstep (se 1 (by rfl) ⟨1155986, by rfl⟩ : syracuseStep 1541315 = 2311973) B2311973
theorem B5268689 : Blo 1539967 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B2311379 : Blo 1539967 2311379 := bstep (se 1 (by rfl) ⟨1733534, by rfl⟩ : syracuseStep 2311379 = 3467069) B3467069
theorem B1541331 : Blo 1539967 1541331 := bstep (se 1 (by rfl) ⟨1155998, by rfl⟩ : syracuseStep 1541331 = 2311997) B2311997
theorem B1541347 : Blo 1539967 1541347 := bstep (se 1 (by rfl) ⟨1156010, by rfl⟩ : syracuseStep 1541347 = 2312021) B2312021
theorem B2311409 : Blo 1539967 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B1541363 : Blo 1539967 1541363 := bstep (se 1 (by rfl) ⟨1156022, by rfl⟩ : syracuseStep 1541363 = 2312045) B2312045
theorem B2311427 : Blo 1539967 2311427 := bstep (se 1 (by rfl) ⟨1733570, by rfl⟩ : syracuseStep 2311427 = 3467141) B3467141
theorem B1541379 : Blo 1539967 1541379 := bstep (se 1 (by rfl) ⟨1156034, by rfl⟩ : syracuseStep 1541379 = 2312069) B2312069
theorem B1541395 : Blo 1539967 1541395 := bstep (se 1 (by rfl) ⟨1156046, by rfl⟩ : syracuseStep 1541395 = 2312093) B2312093
theorem B2311457 : Blo 1539967 2311457 := bstep (se 2 (by rfl) ⟨866796, by rfl⟩ : syracuseStep 2311457 = 1733593) B1733593
theorem B2082083 : Blo 1539967 2082083 := bstep (se 1 (by rfl) ⟨1561562, by rfl⟩ : syracuseStep 2082083 = 3123125) B3123125
theorem B3900707 : Blo 1539967 3900707 := bstep (se 1 (by rfl) ⟨2925530, by rfl⟩ : syracuseStep 3900707 = 5851061) B5851061
theorem B1541411 : Blo 1539967 1541411 := bstep (se 1 (by rfl) ⟨1156058, by rfl⟩ : syracuseStep 1541411 = 2312117) B2312117
theorem B2311475 : Blo 1539967 2311475 := bstep (se 1 (by rfl) ⟨1733606, by rfl⟩ : syracuseStep 2311475 = 3467213) B3467213
theorem B1541427 : Blo 1539967 1541427 := bstep (se 1 (by rfl) ⟨1156070, by rfl⟩ : syracuseStep 1541427 = 2312141) B2312141
theorem B1541443 : Blo 1539967 1541443 := bstep (se 1 (by rfl) ⟨1156082, by rfl⟩ : syracuseStep 1541443 = 2312165) B2312165
theorem B2311505 : Blo 1539967 2311505 := bstep (se 2 (by rfl) ⟨866814, by rfl⟩ : syracuseStep 2311505 = 1733629) B1733629
theorem B1541459 : Blo 1539967 1541459 := bstep (se 1 (by rfl) ⟨1156094, by rfl⟩ : syracuseStep 1541459 = 2312189) B2312189
theorem B2311523 : Blo 1539967 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B2467187 : Blo 1539967 2467187 := bstep (se 1 (by rfl) ⟨1850390, by rfl⟩ : syracuseStep 2467187 = 3700781) B3700781
theorem B2311553 : Blo 1539967 2311553 := bstep (se 2 (by rfl) ⟨866832, by rfl⟩ : syracuseStep 2311553 = 1733665) B1733665
theorem B33326477 : Blo 1539967 33326477 := bstep (se 3 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 33326477 = 12497429) B12497429
theorem B2311571 : Blo 1539967 2311571 := bstep (se 1 (by rfl) ⟨1733678, by rfl⟩ : syracuseStep 2311571 = 3467357) B3467357
theorem B3466673 : Blo 1539967 3466673 := bstep (se 2 (by rfl) ⟨1300002, by rfl⟩ : syracuseStep 3466673 = 2600005) B2600005
theorem B2311601 : Blo 1539967 2311601 := bstep (se 2 (by rfl) ⟨866850, by rfl⟩ : syracuseStep 2311601 = 1733701) B1733701
theorem B3466691 : Blo 1539967 3466691 := bstep (se 1 (by rfl) ⟨2600018, by rfl⟩ : syracuseStep 3466691 = 5200037) B5200037
theorem B2311619 : Blo 1539967 2311619 := bstep (se 1 (by rfl) ⟨1733714, by rfl⟩ : syracuseStep 2311619 = 3467429) B3467429
theorem B2311649 : Blo 1539967 2311649 := bstep (se 2 (by rfl) ⟨866868, by rfl⟩ : syracuseStep 2311649 = 1733737) B1733737
theorem B3900899 : Blo 1539967 3900899 := bstep (se 1 (by rfl) ⟨2925674, by rfl⟩ : syracuseStep 3900899 = 5851349) B5851349
theorem B2311667 : Blo 1539967 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B2311697 : Blo 1539967 2311697 := bstep (se 2 (by rfl) ⟨866886, by rfl⟩ : syracuseStep 2311697 = 1733773) B1733773
theorem B2311715 : Blo 1539967 2311715 := bstep (se 1 (by rfl) ⟨1733786, by rfl⟩ : syracuseStep 2311715 = 3467573) B3467573
theorem B2926115 : Blo 1539967 2926115 := bstep (se 1 (by rfl) ⟨2194586, by rfl⟩ : syracuseStep 2926115 = 4389173) B4389173
theorem B2311745 : Blo 1539967 2311745 := bstep (se 2 (by rfl) ⟨866904, by rfl⟩ : syracuseStep 2311745 = 1733809) B1733809
theorem B2311763 : Blo 1539967 2311763 := bstep (se 1 (by rfl) ⟨1733822, by rfl⟩ : syracuseStep 2311763 = 3467645) B3467645
theorem B2311793 : Blo 1539967 2311793 := bstep (se 2 (by rfl) ⟨866922, by rfl⟩ : syracuseStep 2311793 = 1733845) B1733845
theorem B2311811 : Blo 1539967 2311811 := bstep (se 1 (by rfl) ⟨1733858, by rfl⟩ : syracuseStep 2311811 = 3467717) B3467717
theorem B7800461 : Blo 1539967 7800461 := bstep (se 3 (by rfl) ⟨1462586, by rfl⟩ : syracuseStep 7800461 = 2925173) B2925173
theorem B2311841 : Blo 1539967 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B2311859 : Blo 1539967 2311859 := bstep (se 1 (by rfl) ⟨1733894, by rfl⟩ : syracuseStep 2311859 = 3467789) B3467789
theorem B13158085 : Blo 1539967 13158085 := bstep (se 4 (by rfl) ⟨1233570, by rfl⟩ : syracuseStep 13158085 = 2467141) B2467141
theorem B3466961 : Blo 1539967 3466961 := bstep (se 2 (by rfl) ⟨1300110, by rfl⟩ : syracuseStep 3466961 = 2600221) B2600221
theorem B2311889 : Blo 1539967 2311889 := bstep (se 2 (by rfl) ⟨866958, by rfl⟩ : syracuseStep 2311889 = 1733917) B1733917
theorem B3466979 : Blo 1539967 3466979 := bstep (se 1 (by rfl) ⟨2600234, by rfl⟩ : syracuseStep 3466979 = 5200469) B5200469
theorem B2311907 : Blo 1539967 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B2311937 : Blo 1539967 2311937 := bstep (se 2 (by rfl) ⟨866976, by rfl⟩ : syracuseStep 2311937 = 1733953) B1733953
theorem B5850893 : Blo 1539967 5850893 := bstep (se 3 (by rfl) ⟨1097042, by rfl⟩ : syracuseStep 5850893 = 2194085) B2194085
theorem B2311955 : Blo 1539967 2311955 := bstep (se 1 (by rfl) ⟨1733966, by rfl⟩ : syracuseStep 2311955 = 3467933) B3467933
theorem B2311985 : Blo 1539967 2311985 := bstep (se 2 (by rfl) ⟨866994, by rfl⟩ : syracuseStep 2311985 = 1733989) B1733989
theorem B2312003 : Blo 1539967 2312003 := bstep (se 1 (by rfl) ⟨1734002, by rfl⟩ : syracuseStep 2312003 = 3468005) B3468005
theorem B2312033 : Blo 1539967 2312033 := bstep (se 2 (by rfl) ⟨867012, by rfl⟩ : syracuseStep 2312033 = 1734025) B1734025
theorem B2312051 : Blo 1539967 2312051 := bstep (se 1 (by rfl) ⟨1734038, by rfl⟩ : syracuseStep 2312051 = 3468077) B3468077
theorem B2312081 : Blo 1539967 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B2598817 : Blo 1539967 2598817 := bstep (se 2 (by rfl) ⟨974556, by rfl⟩ : syracuseStep 2598817 = 1949113) B1949113
theorem B2312099 : Blo 1539967 2312099 := bstep (se 1 (by rfl) ⟨1734074, by rfl⟩ : syracuseStep 2312099 = 3468149) B3468149
theorem B2312129 : Blo 1539967 2312129 := bstep (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) B1734097
theorem B2598851 : Blo 1539967 2598851 := bstep (se 1 (by rfl) ⟨1949138, by rfl⟩ : syracuseStep 2598851 = 3898277) B3898277
theorem B2312147 : Blo 1539967 2312147 := bstep (se 1 (by rfl) ⟨1734110, by rfl⟩ : syracuseStep 2312147 = 3468221) B3468221
theorem B3467249 : Blo 1539967 3467249 := bstep (se 2 (by rfl) ⟨1300218, by rfl⟩ : syracuseStep 3467249 = 2600437) B2600437
theorem B2312177 : Blo 1539967 2312177 := bstep (se 2 (by rfl) ⟨867066, by rfl⟩ : syracuseStep 2312177 = 1734133) B1734133
theorem B3467267 : Blo 1539967 3467267 := bstep (se 1 (by rfl) ⟨2600450, by rfl⟩ : syracuseStep 3467267 = 5200901) B5200901
theorem B2312195 : Blo 1539967 2312195 := bstep (se 1 (by rfl) ⟨1734146, by rfl⟩ : syracuseStep 2312195 = 3468293) B3468293
theorem B4933667 : Blo 1539967 4933667 := bstep (se 1 (by rfl) ⟨3700250, by rfl⟩ : syracuseStep 4933667 = 7400501) B7400501
theorem B6580273 : Blo 1539967 6580273 := bstep (se 2 (by rfl) ⟨2467602, by rfl⟩ : syracuseStep 6580273 = 4935205) B4935205
theorem B2598979 : Blo 1539967 2598979 := bstep (se 1 (by rfl) ⟨1949234, by rfl⟩ : syracuseStep 2598979 = 3898469) B3898469
theorem B9873485 : Blo 1539967 9873485 := bstep (se 3 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 9873485 = 3702557) B3702557
theorem B2599121 : Blo 1539967 2599121 := bstep (se 2 (by rfl) ⟨974670, by rfl⟩ : syracuseStep 2599121 = 1949341) B1949341
theorem B13166833 : Blo 1539967 13166833 := bstep (se 2 (by rfl) ⟨4937562, by rfl⟩ : syracuseStep 13166833 = 9875125) B9875125
theorem B4163843 : Blo 1539967 4163843 := bstep (se 1 (by rfl) ⟨3122882, by rfl⟩ : syracuseStep 4163843 = 6245765) B6245765
theorem B3467537 : Blo 1539967 3467537 := bstep (se 2 (by rfl) ⟨1300326, by rfl⟩ : syracuseStep 3467537 = 2600653) B2600653
theorem B3467555 : Blo 1539967 3467555 := bstep (se 1 (by rfl) ⟨2600666, by rfl⟩ : syracuseStep 3467555 = 5201333) B5201333
theorem B2468161 : Blo 1539967 2468161 := bstep (se 2 (by rfl) ⟨925560, by rfl⟩ : syracuseStep 2468161 = 1851121) B1851121
theorem B2599249 : Blo 1539967 2599249 := bstep (se 2 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 2599249 = 1949437) B1949437
theorem B2599283 : Blo 1539967 2599283 := bstep (se 1 (by rfl) ⟨1949462, by rfl⟩ : syracuseStep 2599283 = 3898925) B3898925
theorem B3901841 : Blo 1539967 3901841 := bstep (se 2 (by rfl) ⟨1463190, by rfl⟩ : syracuseStep 3901841 = 2926381) B2926381
theorem B2599411 : Blo 1539967 2599411 := bstep (se 1 (by rfl) ⟨1949558, by rfl⟩ : syracuseStep 2599411 = 3899117) B3899117
theorem B3467825 : Blo 1539967 3467825 := bstep (se 2 (by rfl) ⟨1300434, by rfl⟩ : syracuseStep 3467825 = 2600869) B2600869
theorem B3467843 : Blo 1539967 3467843 := bstep (se 1 (by rfl) ⟨2600882, by rfl⟩ : syracuseStep 3467843 = 5201765) B5201765
theorem B8440433 : Blo 1539967 8440433 := bstep (se 2 (by rfl) ⟨3165162, by rfl⟩ : syracuseStep 8440433 = 6330325) B6330325
theorem B2599553 : Blo 1539967 2599553 := bstep (se 2 (by rfl) ⟨974832, by rfl⟩ : syracuseStep 2599553 = 1949665) B1949665
theorem B5073635 : Blo 1539967 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B20007665 : Blo 1539967 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B2599681 : Blo 1539967 2599681 := bstep (se 2 (by rfl) ⟨974880, by rfl⟩ : syracuseStep 2599681 = 1949761) B1949761
theorem B2599715 : Blo 1539967 2599715 := bstep (se 1 (by rfl) ⟨1949786, by rfl⟩ : syracuseStep 2599715 = 3899573) B3899573
theorem B3468113 : Blo 1539967 3468113 := bstep (se 2 (by rfl) ⟨1300542, by rfl⟩ : syracuseStep 3468113 = 2601085) B2601085
theorem B3468131 : Blo 1539967 3468131 := bstep (se 1 (by rfl) ⟨2601098, by rfl⟩ : syracuseStep 3468131 = 5202197) B5202197
theorem B3124099 : Blo 1539967 3124099 := bstep (se 1 (by rfl) ⟨2343074, by rfl⟩ : syracuseStep 3124099 = 4686149) B4686149
theorem B2599843 : Blo 1539967 2599843 := bstep (se 1 (by rfl) ⟨1949882, by rfl⟩ : syracuseStep 2599843 = 3899765) B3899765
theorem B2599985 : Blo 1539967 2599985 := bstep (se 2 (by rfl) ⟨974994, by rfl⟩ : syracuseStep 2599985 = 1949989) B1949989
theorem B5139533 : Blo 1539967 5139533 := bstep (se 3 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 5139533 = 1927325) B1927325
theorem B2706577 : Blo 1539967 2706577 := bstep (se 2 (by rfl) ⟨1014966, by rfl⟩ : syracuseStep 2706577 = 2029933) B2029933
theorem B2600113 : Blo 1539967 2600113 := bstep (se 2 (by rfl) ⟨975042, by rfl⟩ : syracuseStep 2600113 = 1950085) B1950085
theorem B2600147 : Blo 1539967 2600147 := bstep (se 1 (by rfl) ⟨1950110, by rfl⟩ : syracuseStep 2600147 = 3900221) B3900221
theorem B2469089 : Blo 1539967 2469089 := bstep (se 2 (by rfl) ⟨925908, by rfl⟩ : syracuseStep 2469089 = 1851817) B1851817
theorem B63253781 : Blo 1539967 63253781 := bstep (se 6 (by rfl) ⟨1482510, by rfl⟩ : syracuseStep 63253781 = 2965021) B2965021
theorem B2600275 : Blo 1539967 2600275 := bstep (se 1 (by rfl) ⟨1950206, by rfl⟩ : syracuseStep 2600275 = 3900413) B3900413
theorem B14806385 : Blo 1539967 14806385 := bstep (se 2 (by rfl) ⟨5552394, by rfl⟩ : syracuseStep 14806385 = 11104789) B11104789
theorem B4386257 : Blo 1539967 4386257 := bstep (se 2 (by rfl) ⟨1644846, by rfl⟩ : syracuseStep 4386257 = 3289693) B3289693
theorem B2600417 : Blo 1539967 2600417 := bstep (se 2 (by rfl) ⟨975156, by rfl⟩ : syracuseStep 2600417 = 1950313) B1950313
theorem B7400945 : Blo 1539967 7400945 := bstep (se 2 (by rfl) ⟨2775354, by rfl⟩ : syracuseStep 7400945 = 5550709) B5550709
theorem B2600545 : Blo 1539967 2600545 := bstep (se 2 (by rfl) ⟨975204, by rfl⟩ : syracuseStep 2600545 = 1950409) B1950409
theorem B2600579 : Blo 1539967 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B4165283 : Blo 1539967 4165283 := bstep (se 1 (by rfl) ⟨3123962, by rfl⟩ : syracuseStep 4165283 = 6247925) B6247925
theorem B5197553 : Blo 1539967 5197553 := bstep (se 2 (by rfl) ⟨1949082, by rfl⟩ : syracuseStep 5197553 = 3898165) B3898165
theorem B2223859 : Blo 1539967 2223859 := bstep (se 1 (by rfl) ⟨1667894, by rfl⟩ : syracuseStep 2223859 = 3335789) B3335789
theorem B2600707 : Blo 1539967 2600707 := bstep (se 1 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 2600707 = 3901061) B3901061
theorem B4935437 : Blo 1539967 4935437 := bstep (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) B1850789
theorem B9367331 : Blo 1539967 9367331 := bstep (se 1 (by rfl) ⟨7025498, by rfl⟩ : syracuseStep 9367331 = 14050997) B14050997
theorem B2600849 : Blo 1539967 2600849 := bstep (se 2 (by rfl) ⟨975318, by rfl⟩ : syracuseStep 2600849 = 1950637) B1950637
theorem B1732531 : Blo 1539967 1732531 := bstep (se 1 (by rfl) ⟨1299398, by rfl⟩ : syracuseStep 1732531 = 2598797) B2598797
theorem B19738565 : Blo 1539967 19738565 := bstep (se 4 (by rfl) ⟨1850490, by rfl⟩ : syracuseStep 19738565 = 3700981) B3700981
theorem B2600977 : Blo 1539967 2600977 := bstep (se 2 (by rfl) ⟨975366, by rfl⟩ : syracuseStep 2600977 = 1950733) B1950733
theorem B4165681 : Blo 1539967 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B2601011 : Blo 1539967 2601011 := bstep (se 1 (by rfl) ⟨1950758, by rfl⟩ : syracuseStep 2601011 = 3901517) B3901517
theorem B1732675 : Blo 1539967 1732675 := bstep (se 1 (by rfl) ⟨1299506, by rfl⟩ : syracuseStep 1732675 = 2599013) B2599013
theorem B2601139 : Blo 1539967 2601139 := bstep (se 1 (by rfl) ⟨1950854, by rfl⟩ : syracuseStep 2601139 = 3901709) B3901709
theorem B1732819 : Blo 1539967 1732819 := bstep (se 1 (by rfl) ⟨1299614, by rfl⟩ : syracuseStep 1732819 = 2599229) B2599229
theorem B5198093 : Blo 1539967 5198093 := bstep (se 3 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 5198093 = 1949285) B1949285
theorem B5198147 : Blo 1539967 5198147 := bstep (se 1 (by rfl) ⟨3898610, by rfl⟩ : syracuseStep 5198147 = 7797221) B7797221
theorem B1732963 : Blo 1539967 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B4387213 : Blo 1539967 4387213 := bstep (se 3 (by rfl) ⟨822602, by rfl⟩ : syracuseStep 4387213 = 1645205) B1645205
theorem B1560979 : Blo 1539967 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B7803377 : Blo 1539967 7803377 := bstep (se 2 (by rfl) ⟨2926266, by rfl⟩ : syracuseStep 7803377 = 5852533) B5852533
theorem B1733107 : Blo 1539967 1733107 := bstep (se 1 (by rfl) ⟨1299830, by rfl⟩ : syracuseStep 1733107 = 2599661) B2599661
theorem B4166147 : Blo 1539967 4166147 := bstep (se 1 (by rfl) ⟨3124610, by rfl⟩ : syracuseStep 4166147 = 6249221) B6249221
theorem B8778253 : Blo 1539967 8778253 := bstep (se 3 (by rfl) ⟨1645922, by rfl⟩ : syracuseStep 8778253 = 3291845) B3291845
theorem B3166787 : Blo 1539967 3166787 := bstep (se 1 (by rfl) ⟨2375090, by rfl⟩ : syracuseStep 3166787 = 4750181) B4750181
theorem B5198417 : Blo 1539967 5198417 := bstep (se 2 (by rfl) ⟨1949406, by rfl⟩ : syracuseStep 5198417 = 3898813) B3898813
theorem B4387441 : Blo 1539967 4387441 := bstep (se 2 (by rfl) ⟨1645290, by rfl⟩ : syracuseStep 4387441 = 3290581) B3290581
theorem B1733251 : Blo 1539967 1733251 := bstep (se 1 (by rfl) ⟨1299938, by rfl⟩ : syracuseStep 1733251 = 2599877) B2599877
theorem B2708147 : Blo 1539967 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B2634481 : Blo 1539967 2634481 := bstep (se 2 (by rfl) ⟨987930, by rfl⟩ : syracuseStep 2634481 = 1975861) B1975861
theorem B4387601 : Blo 1539967 4387601 := bstep (se 2 (by rfl) ⟨1645350, by rfl⟩ : syracuseStep 4387601 = 3290701) B3290701
theorem B1733395 : Blo 1539967 1733395 := bstep (se 1 (by rfl) ⟨1300046, by rfl⟩ : syracuseStep 1733395 = 2600093) B2600093
theorem B4387715 : Blo 1539967 4387715 := bstep (se 1 (by rfl) ⟨3290786, by rfl⟩ : syracuseStep 4387715 = 6581573) B6581573
theorem B1733539 : Blo 1539967 1733539 := bstep (se 1 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 1733539 = 2600309) B2600309
theorem B12489713 : Blo 1539967 12489713 := bstep (se 2 (by rfl) ⟨4683642, by rfl⟩ : syracuseStep 12489713 = 9367285) B9367285
theorem B5272561 : Blo 1539967 5272561 := bstep (se 2 (by rfl) ⟨1977210, by rfl⟩ : syracuseStep 5272561 = 3954421) B3954421
theorem B3290129 : Blo 1539967 3290129 := bstep (se 2 (by rfl) ⟨1233798, by rfl⟩ : syracuseStep 3290129 = 2467597) B2467597
theorem B9868337 : Blo 1539967 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B1733683 : Blo 1539967 1733683 := bstep (se 1 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 1733683 = 2600525) B2600525
theorem B11703365 : Blo 1539967 11703365 := bstep (se 4 (by rfl) ⟨1097190, by rfl⟩ : syracuseStep 11703365 = 2194381) B2194381
theorem B5198957 : Blo 1539967 5198957 := bstep (se 3 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 5198957 = 1949609) B1949609
theorem B2110579 : Blo 1539967 2110579 := bstep (se 1 (by rfl) ⟨1582934, by rfl⟩ : syracuseStep 2110579 = 3165869) B3165869
theorem B5199011 : Blo 1539967 5199011 := bstep (se 1 (by rfl) ⟨3899258, by rfl⟩ : syracuseStep 5199011 = 7798517) B7798517
theorem B1733827 : Blo 1539967 1733827 := bstep (se 1 (by rfl) ⟨1300370, by rfl⟩ : syracuseStep 1733827 = 2600741) B2600741
theorem B2192707 : Blo 1539967 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B1733971 : Blo 1539967 1733971 := bstep (se 1 (by rfl) ⟨1300478, by rfl⟩ : syracuseStep 1733971 = 2600957) B2600957
theorem B5199281 : Blo 1539967 5199281 := bstep (se 2 (by rfl) ⟨1949730, by rfl⟩ : syracuseStep 5199281 = 3899461) B3899461
theorem B1734115 : Blo 1539967 1734115 := bstep (se 1 (by rfl) ⟨1300586, by rfl⟩ : syracuseStep 1734115 = 2601173) B2601173
theorem B6583949 : Blo 1539967 6583949 := bstep (se 3 (by rfl) ⟨1234490, by rfl⟩ : syracuseStep 6583949 = 2468981) B2468981
theorem B4683473 : Blo 1539967 4683473 := bstep (se 2 (by rfl) ⟨1756302, by rfl⟩ : syracuseStep 4683473 = 3512605) B3512605
theorem B14808845 : Blo 1539967 14808845 := bstep (se 3 (by rfl) ⟨2776658, by rfl⟩ : syracuseStep 14808845 = 5553317) B5553317
theorem B3700579 : Blo 1539967 3700579 := bstep (se 1 (by rfl) ⟨2775434, by rfl⟩ : syracuseStep 3700579 = 5550869) B5550869
theorem B4388717 : Blo 1539967 4388717 := bstep (se 3 (by rfl) ⟨822884, by rfl⟩ : syracuseStep 4388717 = 1645769) B1645769
theorem B2193265 : Blo 1539967 2193265 := bstep (se 2 (by rfl) ⟨822474, by rfl⟩ : syracuseStep 2193265 = 1644949) B1644949
theorem B3291025 : Blo 1539967 3291025 := bstep (se 2 (by rfl) ⟨1234134, by rfl⟩ : syracuseStep 3291025 = 2468269) B2468269
theorem B3291043 : Blo 1539967 3291043 := bstep (se 1 (by rfl) ⟨2468282, by rfl⟩ : syracuseStep 3291043 = 4936565) B4936565
theorem B5199821 : Blo 1539967 5199821 := bstep (se 3 (by rfl) ⟨974966, by rfl⟩ : syracuseStep 5199821 = 1949933) B1949933
theorem B5199875 : Blo 1539967 5199875 := bstep (se 1 (by rfl) ⟨3899906, by rfl⟩ : syracuseStep 5199875 = 7799813) B7799813
theorem B4388899 : Blo 1539967 4388899 := bstep (se 1 (by rfl) ⟨3291674, by rfl⟩ : syracuseStep 4388899 = 6583349) B6583349
theorem B4389059 : Blo 1539967 4389059 := bstep (se 1 (by rfl) ⟨3291794, by rfl⟩ : syracuseStep 4389059 = 6583589) B6583589
theorem B5200145 : Blo 1539967 5200145 := bstep (se 2 (by rfl) ⟨1950054, by rfl⟩ : syracuseStep 5200145 = 3900109) B3900109
theorem B17545571 : Blo 1539967 17545571 := bstep (se 1 (by rfl) ⟨13159178, by rfl⟩ : syracuseStep 17545571 = 26318357) B26318357
theorem B9869795 : Blo 1539967 9869795 := bstep (se 1 (by rfl) ⟨7402346, by rfl⟩ : syracuseStep 9869795 = 14804693) B14804693
theorem B2193971 : Blo 1539967 2193971 := bstep (se 1 (by rfl) ⟨1645478, by rfl⟩ : syracuseStep 2193971 = 3290957) B3290957
theorem B17357453 : Blo 1539967 17357453 := bstep (se 3 (by rfl) ⟨3254522, by rfl⟩ : syracuseStep 17357453 = 6509045) B6509045
theorem B3898115 : Blo 1539967 3898115 := bstep (se 1 (by rfl) ⟨2923586, by rfl⟩ : syracuseStep 3898115 = 5847173) B5847173
theorem B94878485 : Blo 1539967 94878485 := bstep (se 6 (by rfl) ⟨2223714, by rfl⟩ : syracuseStep 94878485 = 4447429) B4447429
theorem B5200685 : Blo 1539967 5200685 := bstep (se 3 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 5200685 = 1950257) B1950257
theorem B8772421 : Blo 1539967 8772421 := bstep (se 4 (by rfl) ⟨822414, by rfl⟩ : syracuseStep 8772421 = 1644829) B1644829
theorem B5200739 : Blo 1539967 5200739 := bstep (se 1 (by rfl) ⟨3900554, by rfl⟩ : syracuseStep 5200739 = 7801109) B7801109
theorem B2775953 : Blo 1539967 2775953 := bstep (se 2 (by rfl) ⟨1040982, by rfl⟩ : syracuseStep 2775953 = 2081965) B2081965
theorem B3898307 : Blo 1539967 3898307 := bstep (se 1 (by rfl) ⟨2923730, by rfl⟩ : syracuseStep 3898307 = 5847461) B5847461
theorem B17628131 : Blo 1539967 17628131 := bstep (se 1 (by rfl) ⟨13221098, by rfl⟩ : syracuseStep 17628131 = 26442197) B26442197
theorem B4815949 : Blo 1539967 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B2964593 : Blo 1539967 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B5201009 : Blo 1539967 5201009 := bstep (se 2 (by rfl) ⟨1950378, by rfl⟩ : syracuseStep 5201009 = 3900757) B3900757
theorem B2194609 : Blo 1539967 2194609 := bstep (se 2 (by rfl) ⟨822978, by rfl⟩ : syracuseStep 2194609 = 1645957) B1645957
theorem B2923715 : Blo 1539967 2923715 := bstep (se 1 (by rfl) ⟨2192786, by rfl⟩ : syracuseStep 2923715 = 4385573) B4385573
theorem B1645795 : Blo 1539967 1645795 := bstep (se 1 (by rfl) ⟨1234346, by rfl⟩ : syracuseStep 1645795 = 2468693) B2468693
theorem B14253283 : Blo 1539967 14253283 := bstep (se 1 (by rfl) ⟨10689962, by rfl⟩ : syracuseStep 14253283 = 21379925) B21379925
theorem B3702019 : Blo 1539967 3702019 := bstep (se 1 (by rfl) ⟨2776514, by rfl⟩ : syracuseStep 3702019 = 5553029) B5553029
theorem B60833045 : Blo 1539967 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B2194723 : Blo 1539967 2194723 := bstep (se 1 (by rfl) ⟨1646042, by rfl⟩ : syracuseStep 2194723 = 3292085) B3292085
theorem B4685165 : Blo 1539967 4685165 := bstep (se 3 (by rfl) ⟨878468, by rfl⟩ : syracuseStep 4685165 = 1756937) B1756937
theorem B5848433 : Blo 1539967 5848433 := bstep (se 2 (by rfl) ⟨2193162, by rfl⟩ : syracuseStep 5848433 = 4386325) B4386325
theorem B2964899 : Blo 1539967 2964899 := bstep (se 1 (by rfl) ⟨2223674, by rfl⟩ : syracuseStep 2964899 = 4447349) B4447349
theorem B7798193 : Blo 1539967 7798193 := bstep (se 2 (by rfl) ⟨2924322, by rfl⟩ : syracuseStep 7798193 = 5848645) B5848645
theorem B1949123 : Blo 1539967 1949123 := bstep (se 1 (by rfl) ⟨1461842, by rfl⟩ : syracuseStep 1949123 = 2923685) B2923685
theorem B5414381 : Blo 1539967 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B2342515 : Blo 1539967 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B5201549 : Blo 1539967 5201549 := bstep (se 3 (by rfl) ⟨975290, by rfl⟩ : syracuseStep 5201549 = 1950581) B1950581
theorem B5201603 : Blo 1539967 5201603 := bstep (se 1 (by rfl) ⟨3901202, by rfl⟩ : syracuseStep 5201603 = 7802405) B7802405
theorem B3464945 : Blo 1539967 3464945 := bstep (se 2 (by rfl) ⟨1299354, by rfl⟩ : syracuseStep 3464945 = 2598709) B2598709
theorem B3464963 : Blo 1539967 3464963 := bstep (se 1 (by rfl) ⟨2598722, by rfl⟩ : syracuseStep 3464963 = 5197445) B5197445
theorem B2309969 : Blo 1539967 2309969 := bstep (se 2 (by rfl) ⟨866238, by rfl⟩ : syracuseStep 2309969 = 1732477) B1732477
theorem B2309987 : Blo 1539967 2309987 := bstep (se 1 (by rfl) ⟨1732490, by rfl⟩ : syracuseStep 2309987 = 3464981) B3464981
theorem B11698019 : Blo 1539967 11698019 := bstep (se 1 (by rfl) ⟨8773514, by rfl⟩ : syracuseStep 11698019 = 17547029) B17547029
theorem B3899249 : Blo 1539967 3899249 := bstep (se 2 (by rfl) ⟨1462218, by rfl⟩ : syracuseStep 3899249 = 2924437) B2924437
theorem B2310017 : Blo 1539967 2310017 := bstep (se 2 (by rfl) ⟨866256, by rfl⟩ : syracuseStep 2310017 = 1732513) B1732513
theorem B1539971 : Blo 1539967 1539971 := bstep (se 1 (by rfl) ⟨1154978, by rfl⟩ : syracuseStep 1539971 = 2309957) B2309957
theorem B1539987 : Blo 1539967 1539987 := bstep (se 1 (by rfl) ⟨1154990, by rfl⟩ : syracuseStep 1539987 = 2309981) B2309981
theorem B2310035 : Blo 1539967 2310035 := bstep (se 1 (by rfl) ⟨1732526, by rfl⟩ : syracuseStep 2310035 = 3465053) B3465053
theorem B3899299 : Blo 1539967 3899299 := bstep (se 1 (by rfl) ⟨2924474, by rfl⟩ : syracuseStep 3899299 = 5848949) B5848949
theorem B1540003 : Blo 1539967 1540003 := bstep (se 1 (by rfl) ⟨1155002, by rfl⟩ : syracuseStep 1540003 = 2310005) B2310005
theorem B2310065 : Blo 1539967 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B1540019 : Blo 1539967 1540019 := bstep (se 1 (by rfl) ⟨1155014, by rfl⟩ : syracuseStep 1540019 = 2310029) B2310029
theorem B1540035 : Blo 1539967 1540035 := bstep (se 1 (by rfl) ⟨1155026, by rfl⟩ : syracuseStep 1540035 = 2310053) B2310053
theorem B2310083 : Blo 1539967 2310083 := bstep (se 1 (by rfl) ⟨1732562, by rfl⟩ : syracuseStep 2310083 = 3465125) B3465125
theorem B5201873 : Blo 1539967 5201873 := bstep (se 2 (by rfl) ⟨1950702, by rfl⟩ : syracuseStep 5201873 = 3901405) B3901405
theorem B1540051 : Blo 1539967 1540051 := bstep (se 1 (by rfl) ⟨1155038, by rfl⟩ : syracuseStep 1540051 = 2310077) B2310077
theorem B2310113 : Blo 1539967 2310113 := bstep (se 2 (by rfl) ⟨866292, by rfl⟩ : syracuseStep 2310113 = 1732585) B1732585
theorem B1540067 : Blo 1539967 1540067 := bstep (se 1 (by rfl) ⟨1155050, by rfl⟩ : syracuseStep 1540067 = 2310101) B2310101
theorem B1540083 : Blo 1539967 1540083 := bstep (se 1 (by rfl) ⟨1155062, by rfl⟩ : syracuseStep 1540083 = 2310125) B2310125
theorem B2310131 : Blo 1539967 2310131 := bstep (se 1 (by rfl) ⟨1732598, by rfl⟩ : syracuseStep 2310131 = 3465197) B3465197
theorem B2310155 : Blo 1539967 2310155 := bstep (se 1 (by rfl) ⟨1732616, by rfl⟩ : syracuseStep 2310155 = 3465233) B3465233
theorem B1540107 : Blo 1539967 1540107 := bstep (se 1 (by rfl) ⟨1155080, by rfl⟩ : syracuseStep 1540107 = 2310161) B2310161
theorem B2310167 : Blo 1539967 2310167 := bstep (se 1 (by rfl) ⟨1732625, by rfl⟩ : syracuseStep 2310167 = 3465251) B3465251
theorem B1540119 : Blo 1539967 1540119 := bstep (se 1 (by rfl) ⟨1155089, by rfl⟩ : syracuseStep 1540119 = 2310179) B2310179
theorem B1540139 : Blo 1539967 1540139 := bstep (se 1 (by rfl) ⟨1155104, by rfl⟩ : syracuseStep 1540139 = 2310209) B2310209
theorem B1540151 : Blo 1539967 1540151 := bstep (se 1 (by rfl) ⟨1155113, by rfl⟩ : syracuseStep 1540151 = 2310227) B2310227
theorem B8773697 : Blo 1539967 8773697 := bstep (se 2 (by rfl) ⟨3290136, by rfl⟩ : syracuseStep 8773697 = 6580273) B6580273
theorem B5554241 : Blo 1539967 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B1540171 : Blo 1539967 1540171 := bstep (se 1 (by rfl) ⟨1155128, by rfl⟩ : syracuseStep 1540171 = 2310257) B2310257
theorem B1949771 : Blo 1539967 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B1540183 : Blo 1539967 1540183 := bstep (se 1 (by rfl) ⟨1155137, by rfl⟩ : syracuseStep 1540183 = 2310275) B2310275
theorem B3465305 : Blo 1539967 3465305 := bstep (se 2 (by rfl) ⟨1299489, by rfl⟩ : syracuseStep 3465305 = 2598979) B2598979
theorem B2310233 : Blo 1539967 2310233 := bstep (se 2 (by rfl) ⟨866337, by rfl⟩ : syracuseStep 2310233 = 1732675) B1732675
theorem B13156445 : Blo 1539967 13156445 := bstep (se 3 (by rfl) ⟨2466833, by rfl⟩ : syracuseStep 13156445 = 4933667) B4933667
theorem B1540203 : Blo 1539967 1540203 := bstep (se 1 (by rfl) ⟨1155152, by rfl⟩ : syracuseStep 1540203 = 2310305) B2310305
theorem B1540215 : Blo 1539967 1540215 := bstep (se 1 (by rfl) ⟨1155161, by rfl⟩ : syracuseStep 1540215 = 2310323) B2310323
theorem B1540235 : Blo 1539967 1540235 := bstep (se 1 (by rfl) ⟨1155176, by rfl⟩ : syracuseStep 1540235 = 2310353) B2310353
theorem B1540247 : Blo 1539967 1540247 := bstep (se 1 (by rfl) ⟨1155185, by rfl⟩ : syracuseStep 1540247 = 2310371) B2310371
theorem B1540267 : Blo 1539967 1540267 := bstep (se 1 (by rfl) ⟨1155200, by rfl⟩ : syracuseStep 1540267 = 2310401) B2310401
theorem B3465395 : Blo 1539967 3465395 := bstep (se 1 (by rfl) ⟨2599046, by rfl⟩ : syracuseStep 3465395 = 5198093) B5198093
theorem B1540279 : Blo 1539967 1540279 := bstep (se 1 (by rfl) ⟨1155209, by rfl⟩ : syracuseStep 1540279 = 2310419) B2310419
theorem B2310347 : Blo 1539967 2310347 := bstep (se 1 (by rfl) ⟨1732760, by rfl⟩ : syracuseStep 2310347 = 3465521) B3465521
theorem B1540299 : Blo 1539967 1540299 := bstep (se 1 (by rfl) ⟨1155224, by rfl⟩ : syracuseStep 1540299 = 2310449) B2310449
theorem B13705421 : Blo 1539967 13705421 := bstep (se 3 (by rfl) ⟨2569766, by rfl⟩ : syracuseStep 13705421 = 5139533) B5139533
theorem B3465431 : Blo 1539967 3465431 := bstep (se 1 (by rfl) ⟨2599073, by rfl⟩ : syracuseStep 3465431 = 5198147) B5198147
theorem B2310359 : Blo 1539967 2310359 := bstep (se 1 (by rfl) ⟨1732769, by rfl⟩ : syracuseStep 2310359 = 3465539) B3465539
theorem B1540311 : Blo 1539967 1540311 := bstep (se 1 (by rfl) ⟨1155233, by rfl⟩ : syracuseStep 1540311 = 2310467) B2310467
theorem B1540331 : Blo 1539967 1540331 := bstep (se 1 (by rfl) ⟨1155248, by rfl⟩ : syracuseStep 1540331 = 2310497) B2310497
theorem B1540343 : Blo 1539967 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B1540363 : Blo 1539967 1540363 := bstep (se 1 (by rfl) ⟨1155272, by rfl⟩ : syracuseStep 1540363 = 2310545) B2310545
theorem B1540375 : Blo 1539967 1540375 := bstep (se 1 (by rfl) ⟨1155281, by rfl⟩ : syracuseStep 1540375 = 2310563) B2310563
theorem B2310425 : Blo 1539967 2310425 := bstep (se 2 (by rfl) ⟨866409, by rfl⟩ : syracuseStep 2310425 = 1732819) B1732819
theorem B1540395 : Blo 1539967 1540395 := bstep (se 1 (by rfl) ⟨1155296, by rfl⟩ : syracuseStep 1540395 = 2310593) B2310593
theorem B1540407 : Blo 1539967 1540407 := bstep (se 1 (by rfl) ⟨1155305, by rfl⟩ : syracuseStep 1540407 = 2310611) B2310611
theorem B17555777 : Blo 1539967 17555777 := bstep (se 2 (by rfl) ⟨6583416, by rfl⟩ : syracuseStep 17555777 = 13166833) B13166833
theorem B1540427 : Blo 1539967 1540427 := bstep (se 1 (by rfl) ⟨1155320, by rfl⟩ : syracuseStep 1540427 = 2310641) B2310641
theorem B3703115 : Blo 1539967 3703115 := bstep (se 1 (by rfl) ⟨2777336, by rfl⟩ : syracuseStep 3703115 = 5554673) B5554673
theorem B5202251 : Blo 1539967 5202251 := bstep (se 1 (by rfl) ⟨3901688, by rfl⟩ : syracuseStep 5202251 = 7803377) B7803377
theorem B1540439 : Blo 1539967 1540439 := bstep (se 1 (by rfl) ⟨1155329, by rfl⟩ : syracuseStep 1540439 = 2310659) B2310659
theorem B2777431 : Blo 1539967 2777431 := bstep (se 1 (by rfl) ⟨2083073, by rfl⟩ : syracuseStep 2777431 = 4166147) B4166147
theorem B1540459 : Blo 1539967 1540459 := bstep (se 1 (by rfl) ⟨1155344, by rfl⟩ : syracuseStep 1540459 = 2310689) B2310689
theorem B1540471 : Blo 1539967 1540471 := bstep (se 1 (by rfl) ⟨1155353, by rfl⟩ : syracuseStep 1540471 = 2310707) B2310707
theorem B3465611 : Blo 1539967 3465611 := bstep (se 1 (by rfl) ⟨2599208, by rfl⟩ : syracuseStep 3465611 = 5198417) B5198417
theorem B2310539 : Blo 1539967 2310539 := bstep (se 1 (by rfl) ⟨1732904, by rfl⟩ : syracuseStep 2310539 = 3465809) B3465809
theorem B1540491 : Blo 1539967 1540491 := bstep (se 1 (by rfl) ⟨1155368, by rfl⟩ : syracuseStep 1540491 = 2310737) B2310737
theorem B2310551 : Blo 1539967 2310551 := bstep (se 1 (by rfl) ⟨1732913, by rfl⟩ : syracuseStep 2310551 = 3465827) B3465827
theorem B1540503 : Blo 1539967 1540503 := bstep (se 1 (by rfl) ⟨1155377, by rfl⟩ : syracuseStep 1540503 = 2310755) B2310755
theorem B1540523 : Blo 1539967 1540523 := bstep (se 1 (by rfl) ⟨1155392, by rfl⟩ : syracuseStep 1540523 = 2310785) B2310785
theorem B1540535 : Blo 1539967 1540535 := bstep (se 1 (by rfl) ⟨1155401, by rfl⟩ : syracuseStep 1540535 = 2310803) B2310803
theorem B3465665 : Blo 1539967 3465665 := bstep (se 2 (by rfl) ⟨1299624, by rfl⟩ : syracuseStep 3465665 = 2599249) B2599249
theorem B1540555 : Blo 1539967 1540555 := bstep (se 1 (by rfl) ⟨1155416, by rfl⟩ : syracuseStep 1540555 = 2310833) B2310833
theorem B1540567 : Blo 1539967 1540567 := bstep (se 1 (by rfl) ⟨1155425, by rfl⟩ : syracuseStep 1540567 = 2310851) B2310851
theorem B2310617 : Blo 1539967 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B1540587 : Blo 1539967 1540587 := bstep (se 1 (by rfl) ⟨1155440, by rfl⟩ : syracuseStep 1540587 = 2310881) B2310881
theorem B1540599 : Blo 1539967 1540599 := bstep (se 1 (by rfl) ⟨1155449, by rfl⟩ : syracuseStep 1540599 = 2310899) B2310899
theorem B5849603 : Blo 1539967 5849603 := bstep (se 1 (by rfl) ⟨4387202, by rfl⟩ : syracuseStep 5849603 = 8774405) B8774405
theorem B1540619 : Blo 1539967 1540619 := bstep (se 1 (by rfl) ⟨1155464, by rfl⟩ : syracuseStep 1540619 = 2310929) B2310929
theorem B2925067 : Blo 1539967 2925067 := bstep (se 1 (by rfl) ⟨2193800, by rfl⟩ : syracuseStep 2925067 = 4387601) B4387601
theorem B5849617 : Blo 1539967 5849617 := bstep (se 2 (by rfl) ⟨2193606, by rfl⟩ : syracuseStep 5849617 = 4387213) B4387213
theorem B1540631 : Blo 1539967 1540631 := bstep (se 1 (by rfl) ⟨1155473, by rfl⟩ : syracuseStep 1540631 = 2310947) B2310947
theorem B3899927 : Blo 1539967 3899927 := bstep (se 1 (by rfl) ⟨2924945, by rfl⟩ : syracuseStep 3899927 = 5849891) B5849891
theorem B2081305 : Blo 1539967 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B1540651 : Blo 1539967 1540651 := bstep (se 1 (by rfl) ⟨1155488, by rfl⟩ : syracuseStep 1540651 = 2310977) B2310977
theorem B1540663 : Blo 1539967 1540663 := bstep (se 1 (by rfl) ⟨1155497, by rfl⟩ : syracuseStep 1540663 = 2310995) B2310995
theorem B2310731 : Blo 1539967 2310731 := bstep (se 1 (by rfl) ⟨1733048, by rfl⟩ : syracuseStep 2310731 = 3466097) B3466097
theorem B1540683 : Blo 1539967 1540683 := bstep (se 1 (by rfl) ⟨1155512, by rfl⟩ : syracuseStep 1540683 = 2311025) B2311025
theorem B2310743 : Blo 1539967 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B1540695 : Blo 1539967 1540695 := bstep (se 1 (by rfl) ⟨1155521, by rfl⟩ : syracuseStep 1540695 = 2311043) B2311043
theorem B2925143 : Blo 1539967 2925143 := bstep (se 1 (by rfl) ⟨2193857, by rfl⟩ : syracuseStep 2925143 = 4387715) B4387715
theorem B11256421 : Blo 1539967 11256421 := bstep (se 4 (by rfl) ⟨1055289, by rfl⟩ : syracuseStep 11256421 = 2110579) B2110579
theorem B1540715 : Blo 1539967 1540715 := bstep (se 1 (by rfl) ⟨1155536, by rfl⟩ : syracuseStep 1540715 = 2311073) B2311073
theorem B1540727 : Blo 1539967 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B1540747 : Blo 1539967 1540747 := bstep (se 1 (by rfl) ⟨1155560, by rfl⟩ : syracuseStep 1540747 = 2311121) B2311121
theorem B1540759 : Blo 1539967 1540759 := bstep (se 1 (by rfl) ⟨1155569, by rfl⟩ : syracuseStep 1540759 = 2311139) B2311139
theorem B3465881 : Blo 1539967 3465881 := bstep (se 2 (by rfl) ⟨1299705, by rfl⟩ : syracuseStep 3465881 = 2599411) B2599411
theorem B2310809 : Blo 1539967 2310809 := bstep (se 2 (by rfl) ⟨866553, by rfl⟩ : syracuseStep 2310809 = 1733107) B1733107
theorem B1540779 : Blo 1539967 1540779 := bstep (se 1 (by rfl) ⟨1155584, by rfl⟩ : syracuseStep 1540779 = 2311169) B2311169
theorem B1540791 : Blo 1539967 1540791 := bstep (se 1 (by rfl) ⟨1155593, by rfl⟩ : syracuseStep 1540791 = 2311187) B2311187
theorem B6578891 : Blo 1539967 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B1540811 : Blo 1539967 1540811 := bstep (se 1 (by rfl) ⟨1155608, by rfl⟩ : syracuseStep 1540811 = 2311217) B2311217
theorem B1540823 : Blo 1539967 1540823 := bstep (se 1 (by rfl) ⟨1155617, by rfl⟩ : syracuseStep 1540823 = 2311235) B2311235
theorem B1540843 : Blo 1539967 1540843 := bstep (se 1 (by rfl) ⟨1155632, by rfl⟩ : syracuseStep 1540843 = 2311265) B2311265
theorem B3465971 : Blo 1539967 3465971 := bstep (se 1 (by rfl) ⟨2599478, by rfl⟩ : syracuseStep 3465971 = 5198957) B5198957
theorem B1540855 : Blo 1539967 1540855 := bstep (se 1 (by rfl) ⟨1155641, by rfl⟩ : syracuseStep 1540855 = 2311283) B2311283
theorem B2310923 : Blo 1539967 2310923 := bstep (se 1 (by rfl) ⟨1733192, by rfl⟩ : syracuseStep 2310923 = 3466385) B3466385
theorem B1540875 : Blo 1539967 1540875 := bstep (se 1 (by rfl) ⟨1155656, by rfl⟩ : syracuseStep 1540875 = 2311313) B2311313
theorem B1950475 : Blo 1539967 1950475 := bstep (se 1 (by rfl) ⟨1462856, by rfl⟩ : syracuseStep 1950475 = 2925713) B2925713
theorem B3466007 : Blo 1539967 3466007 := bstep (se 1 (by rfl) ⟨2599505, by rfl⟩ : syracuseStep 3466007 = 5199011) B5199011
theorem B2310935 : Blo 1539967 2310935 := bstep (se 1 (by rfl) ⟨1733201, by rfl⟩ : syracuseStep 2310935 = 3466403) B3466403
theorem B1540887 : Blo 1539967 1540887 := bstep (se 1 (by rfl) ⟨1155665, by rfl⟩ : syracuseStep 1540887 = 2311331) B2311331
theorem B1540907 : Blo 1539967 1540907 := bstep (se 1 (by rfl) ⟨1155680, by rfl⟩ : syracuseStep 1540907 = 2311361) B2311361
theorem B1540919 : Blo 1539967 1540919 := bstep (se 1 (by rfl) ⟨1155689, by rfl⟩ : syracuseStep 1540919 = 2311379) B2311379
theorem B5849921 : Blo 1539967 5849921 := bstep (se 2 (by rfl) ⟨2193720, by rfl⟩ : syracuseStep 5849921 = 4387441) B4387441
theorem B1540939 : Blo 1539967 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B1540951 : Blo 1539967 1540951 := bstep (se 1 (by rfl) ⟨1155713, by rfl⟩ : syracuseStep 1540951 = 2311427) B2311427
theorem B2311001 : Blo 1539967 2311001 := bstep (se 2 (by rfl) ⟨866625, by rfl⟩ : syracuseStep 2311001 = 1733251) B1733251
theorem B1540971 : Blo 1539967 1540971 := bstep (se 1 (by rfl) ⟨1155728, by rfl⟩ : syracuseStep 1540971 = 2311457) B2311457
theorem B1540983 : Blo 1539967 1540983 := bstep (se 1 (by rfl) ⟨1155737, by rfl⟩ : syracuseStep 1540983 = 2311475) B2311475
theorem B1541003 : Blo 1539967 1541003 := bstep (se 1 (by rfl) ⟨1155752, by rfl⟩ : syracuseStep 1541003 = 2311505) B2311505
theorem B1541015 : Blo 1539967 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B1541035 : Blo 1539967 1541035 := bstep (se 1 (by rfl) ⟨1155776, by rfl⟩ : syracuseStep 1541035 = 2311553) B2311553
theorem B22217651 : Blo 1539967 22217651 := bstep (se 1 (by rfl) ⟨16663238, by rfl⟩ : syracuseStep 22217651 = 33326477) B33326477
theorem B1541047 : Blo 1539967 1541047 := bstep (se 1 (by rfl) ⟨1155785, by rfl⟩ : syracuseStep 1541047 = 2311571) B2311571
theorem B3466187 : Blo 1539967 3466187 := bstep (se 1 (by rfl) ⟨2599640, by rfl⟩ : syracuseStep 3466187 = 5199281) B5199281
theorem B2311115 : Blo 1539967 2311115 := bstep (se 1 (by rfl) ⟨1733336, by rfl⟩ : syracuseStep 2311115 = 3466673) B3466673
theorem B1541067 : Blo 1539967 1541067 := bstep (se 1 (by rfl) ⟨1155800, by rfl⟩ : syracuseStep 1541067 = 2311601) B2311601
theorem B2311127 : Blo 1539967 2311127 := bstep (se 1 (by rfl) ⟨1733345, by rfl⟩ : syracuseStep 2311127 = 3466691) B3466691
theorem B1541079 : Blo 1539967 1541079 := bstep (se 1 (by rfl) ⟨1155809, by rfl⟩ : syracuseStep 1541079 = 2311619) B2311619
theorem B1541099 : Blo 1539967 1541099 := bstep (se 1 (by rfl) ⟨1155824, by rfl⟩ : syracuseStep 1541099 = 2311649) B2311649
theorem B1541111 : Blo 1539967 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B3466241 : Blo 1539967 3466241 := bstep (se 2 (by rfl) ⟨1299840, by rfl⟩ : syracuseStep 3466241 = 2599681) B2599681
theorem B1541131 : Blo 1539967 1541131 := bstep (se 1 (by rfl) ⟨1155848, by rfl⟩ : syracuseStep 1541131 = 2311697) B2311697
theorem B1541143 : Blo 1539967 1541143 := bstep (se 1 (by rfl) ⟨1155857, by rfl⟩ : syracuseStep 1541143 = 2311715) B2311715
theorem B1950743 : Blo 1539967 1950743 := bstep (se 1 (by rfl) ⟨1463057, by rfl⟩ : syracuseStep 1950743 = 2926115) B2926115
theorem B2311193 : Blo 1539967 2311193 := bstep (se 2 (by rfl) ⟨866697, by rfl⟩ : syracuseStep 2311193 = 1733395) B1733395
theorem B1541163 : Blo 1539967 1541163 := bstep (se 1 (by rfl) ⟨1155872, by rfl⟩ : syracuseStep 1541163 = 2311745) B2311745
theorem B1541175 : Blo 1539967 1541175 := bstep (se 1 (by rfl) ⟨1155881, by rfl⟩ : syracuseStep 1541175 = 2311763) B2311763
theorem B1541195 : Blo 1539967 1541195 := bstep (se 1 (by rfl) ⟨1155896, by rfl⟩ : syracuseStep 1541195 = 2311793) B2311793
theorem B1541207 : Blo 1539967 1541207 := bstep (se 1 (by rfl) ⟨1155905, by rfl⟩ : syracuseStep 1541207 = 2311811) B2311811
theorem B1541227 : Blo 1539967 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B1541239 : Blo 1539967 1541239 := bstep (se 1 (by rfl) ⟨1155929, by rfl⟩ : syracuseStep 1541239 = 2311859) B2311859
theorem B3122315 : Blo 1539967 3122315 := bstep (se 1 (by rfl) ⟨2341736, by rfl⟩ : syracuseStep 3122315 = 4683473) B4683473
theorem B2311307 : Blo 1539967 2311307 := bstep (se 1 (by rfl) ⟨1733480, by rfl⟩ : syracuseStep 2311307 = 3466961) B3466961
theorem B1541259 : Blo 1539967 1541259 := bstep (se 1 (by rfl) ⟨1155944, by rfl⟩ : syracuseStep 1541259 = 2311889) B2311889
theorem B2311319 : Blo 1539967 2311319 := bstep (se 1 (by rfl) ⟨1733489, by rfl⟩ : syracuseStep 2311319 = 3466979) B3466979
theorem B1541271 : Blo 1539967 1541271 := bstep (se 1 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 1541271 = 2311907) B2311907
theorem B1541291 : Blo 1539967 1541291 := bstep (se 1 (by rfl) ⟨1155968, by rfl⟩ : syracuseStep 1541291 = 2311937) B2311937
theorem B9872563 : Blo 1539967 9872563 := bstep (se 1 (by rfl) ⟨7404422, by rfl⟩ : syracuseStep 9872563 = 14808845) B14808845
theorem B3900595 : Blo 1539967 3900595 := bstep (se 1 (by rfl) ⟨2925446, by rfl⟩ : syracuseStep 3900595 = 5850893) B5850893
theorem B1541303 : Blo 1539967 1541303 := bstep (se 1 (by rfl) ⟨1155977, by rfl⟩ : syracuseStep 1541303 = 2311955) B2311955
theorem B1541323 : Blo 1539967 1541323 := bstep (se 1 (by rfl) ⟨1155992, by rfl⟩ : syracuseStep 1541323 = 2311985) B2311985
theorem B1541335 : Blo 1539967 1541335 := bstep (se 1 (by rfl) ⟨1156001, by rfl⟩ : syracuseStep 1541335 = 2312003) B2312003
theorem B3466457 : Blo 1539967 3466457 := bstep (se 2 (by rfl) ⟨1299921, by rfl⟩ : syracuseStep 3466457 = 2599843) B2599843
theorem B2311385 : Blo 1539967 2311385 := bstep (se 2 (by rfl) ⟨866769, by rfl⟩ : syracuseStep 2311385 = 1733539) B1733539
theorem B1541355 : Blo 1539967 1541355 := bstep (se 1 (by rfl) ⟨1156016, by rfl⟩ : syracuseStep 1541355 = 2312033) B2312033
theorem B2925811 : Blo 1539967 2925811 := bstep (se 1 (by rfl) ⟨2194358, by rfl⟩ : syracuseStep 2925811 = 4388717) B4388717
theorem B1541367 : Blo 1539967 1541367 := bstep (se 1 (by rfl) ⟨1156025, by rfl⟩ : syracuseStep 1541367 = 2312051) B2312051
theorem B11101445 : Blo 1539967 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B59245829 : Blo 1539967 59245829 := bstep (se 4 (by rfl) ⟨5554296, by rfl⟩ : syracuseStep 59245829 = 11108593) B11108593
theorem B1541387 : Blo 1539967 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B1541399 : Blo 1539967 1541399 := bstep (se 1 (by rfl) ⟨1156049, by rfl⟩ : syracuseStep 1541399 = 2312099) B2312099
theorem B1541419 : Blo 1539967 1541419 := bstep (se 1 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 1541419 = 2312129) B2312129
theorem B3466547 : Blo 1539967 3466547 := bstep (se 1 (by rfl) ⟨2599910, by rfl⟩ : syracuseStep 3466547 = 5199821) B5199821
theorem B1541431 : Blo 1539967 1541431 := bstep (se 1 (by rfl) ⟨1156073, by rfl⟩ : syracuseStep 1541431 = 2312147) B2312147
theorem B3900737 : Blo 1539967 3900737 := bstep (se 2 (by rfl) ⟨1462776, by rfl⟩ : syracuseStep 3900737 = 2925553) B2925553
theorem B7030081 : Blo 1539967 7030081 := bstep (se 2 (by rfl) ⟨2636280, by rfl⟩ : syracuseStep 7030081 = 5272561) B5272561
theorem B2311499 : Blo 1539967 2311499 := bstep (se 1 (by rfl) ⟨1733624, by rfl⟩ : syracuseStep 2311499 = 3467249) B3467249
theorem B1541451 : Blo 1539967 1541451 := bstep (se 1 (by rfl) ⟨1156088, by rfl⟩ : syracuseStep 1541451 = 2312177) B2312177
theorem B3466583 : Blo 1539967 3466583 := bstep (se 1 (by rfl) ⟨2599937, by rfl⟩ : syracuseStep 3466583 = 5199875) B5199875
theorem B2311511 : Blo 1539967 2311511 := bstep (se 1 (by rfl) ⟨1733633, by rfl⟩ : syracuseStep 2311511 = 3467267) B3467267
theorem B1541463 : Blo 1539967 1541463 := bstep (se 1 (by rfl) ⟨1156097, by rfl⟩ : syracuseStep 1541463 = 2312195) B2312195
theorem B2311577 : Blo 1539967 2311577 := bstep (se 2 (by rfl) ⟨866841, by rfl⟩ : syracuseStep 2311577 = 1733683) B1733683
theorem B2926039 : Blo 1539967 2926039 := bstep (se 1 (by rfl) ⟨2194529, by rfl⟩ : syracuseStep 2926039 = 4389059) B4389059
theorem B5850589 : Blo 1539967 5850589 := bstep (se 3 (by rfl) ⟨1096985, by rfl⟩ : syracuseStep 5850589 = 2193971) B2193971
theorem B3466763 : Blo 1539967 3466763 := bstep (se 1 (by rfl) ⟨2600072, by rfl⟩ : syracuseStep 3466763 = 5200145) B5200145
theorem B2311691 : Blo 1539967 2311691 := bstep (se 1 (by rfl) ⟨1733768, by rfl⟩ : syracuseStep 2311691 = 3467537) B3467537
theorem B2311703 : Blo 1539967 2311703 := bstep (se 1 (by rfl) ⟨1733777, by rfl⟩ : syracuseStep 2311703 = 3467555) B3467555
theorem B3466817 : Blo 1539967 3466817 := bstep (se 2 (by rfl) ⟨1300056, by rfl⟩ : syracuseStep 3466817 = 2600113) B2600113
theorem B2926145 : Blo 1539967 2926145 := bstep (se 2 (by rfl) ⟨1097304, by rfl⟩ : syracuseStep 2926145 = 2194609) B2194609
theorem B2311769 : Blo 1539967 2311769 := bstep (se 2 (by rfl) ⟨866913, by rfl⟩ : syracuseStep 2311769 = 1733827) B1733827
theorem B6579863 : Blo 1539967 6579863 := bstep (se 1 (by rfl) ⟨4934897, by rfl⟩ : syracuseStep 6579863 = 9869795) B9869795
theorem B2311883 : Blo 1539967 2311883 := bstep (se 1 (by rfl) ⟨1733912, by rfl⟩ : syracuseStep 2311883 = 3467825) B3467825
theorem B2311895 : Blo 1539967 2311895 := bstep (se 1 (by rfl) ⟨1733921, by rfl⟩ : syracuseStep 2311895 = 3467843) B3467843
theorem B2926297 : Blo 1539967 2926297 := bstep (se 2 (by rfl) ⟨1097361, by rfl⟩ : syracuseStep 2926297 = 2194723) B2194723
theorem B3467033 : Blo 1539967 3467033 := bstep (se 2 (by rfl) ⟨1300137, by rfl⟩ : syracuseStep 3467033 = 2600275) B2600275
theorem B2311961 : Blo 1539967 2311961 := bstep (se 2 (by rfl) ⟨866985, by rfl⟩ : syracuseStep 2311961 = 1733971) B1733971
theorem B13338443 : Blo 1539967 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B2598743 : Blo 1539967 2598743 := bstep (se 1 (by rfl) ⟨1949057, by rfl⟩ : syracuseStep 2598743 = 3898115) B3898115
theorem B63252323 : Blo 1539967 63252323 := bstep (se 1 (by rfl) ⟨47439242, by rfl⟩ : syracuseStep 63252323 = 94878485) B94878485
theorem B3467123 : Blo 1539967 3467123 := bstep (se 1 (by rfl) ⟨2600342, by rfl⟩ : syracuseStep 3467123 = 5200685) B5200685
theorem B2312075 : Blo 1539967 2312075 := bstep (se 1 (by rfl) ⟨1734056, by rfl⟩ : syracuseStep 2312075 = 3468113) B3468113
theorem B3467159 : Blo 1539967 3467159 := bstep (se 1 (by rfl) ⟨2600369, by rfl⟩ : syracuseStep 3467159 = 5200739) B5200739
theorem B2312087 : Blo 1539967 2312087 := bstep (se 1 (by rfl) ⟨1734065, by rfl⟩ : syracuseStep 2312087 = 3468131) B3468131
theorem B2598871 : Blo 1539967 2598871 := bstep (se 1 (by rfl) ⟨1949153, by rfl⟩ : syracuseStep 2598871 = 3898307) B3898307
theorem B2312153 : Blo 1539967 2312153 := bstep (se 2 (by rfl) ⟨867057, by rfl⟩ : syracuseStep 2312153 = 1734115) B1734115
theorem B1976395 : Blo 1539967 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B3467339 : Blo 1539967 3467339 := bstep (se 1 (by rfl) ⟨2600504, by rfl⟩ : syracuseStep 3467339 = 5201009) B5201009
theorem B24979549 : Blo 1539967 24979549 := bstep (se 3 (by rfl) ⟨4683665, by rfl⟩ : syracuseStep 24979549 = 9367331) B9367331
theorem B3467393 : Blo 1539967 3467393 := bstep (se 2 (by rfl) ⟨1300272, by rfl⟩ : syracuseStep 3467393 = 2600545) B2600545
theorem B3123353 : Blo 1539967 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B3123443 : Blo 1539967 3123443 := bstep (se 1 (by rfl) ⟨2342582, by rfl⟩ : syracuseStep 3123443 = 4685165) B4685165
theorem B1976599 : Blo 1539967 1976599 := bstep (se 1 (by rfl) ⟨1482449, by rfl⟩ : syracuseStep 1976599 = 2964899) B2964899
theorem B4933963 : Blo 1539967 4933963 := bstep (se 1 (by rfl) ⟨3700472, by rfl⟩ : syracuseStep 4933963 = 7400945) B7400945
theorem B3467609 : Blo 1539967 3467609 := bstep (se 2 (by rfl) ⟨1300353, by rfl⟩ : syracuseStep 3467609 = 2600707) B2600707
theorem B3467699 : Blo 1539967 3467699 := bstep (se 1 (by rfl) ⟨2600774, by rfl⟩ : syracuseStep 3467699 = 5201549) B5201549
theorem B3467735 : Blo 1539967 3467735 := bstep (se 1 (by rfl) ⟨2600801, by rfl⟩ : syracuseStep 3467735 = 5201603) B5201603
theorem B4934105 : Blo 1539967 4934105 := bstep (se 2 (by rfl) ⟨1850289, by rfl⟩ : syracuseStep 4934105 = 3700579) B3700579
theorem B2599499 : Blo 1539967 2599499 := bstep (se 1 (by rfl) ⟨1949624, by rfl⟩ : syracuseStep 2599499 = 3899249) B3899249
theorem B14248549 : Blo 1539967 14248549 := bstep (se 4 (by rfl) ⟨1335801, by rfl⟩ : syracuseStep 14248549 = 2671603) B2671603
theorem B13159043 : Blo 1539967 13159043 := bstep (se 1 (by rfl) ⟨9869282, by rfl⟩ : syracuseStep 13159043 = 19738565) B19738565
theorem B3467915 : Blo 1539967 3467915 := bstep (se 1 (by rfl) ⟨2600936, by rfl⟩ : syracuseStep 3467915 = 5201873) B5201873
theorem B3467969 : Blo 1539967 3467969 := bstep (se 2 (by rfl) ⟨1300488, by rfl⟩ : syracuseStep 3467969 = 2600977) B2600977
theorem B2599627 : Blo 1539967 2599627 := bstep (se 1 (by rfl) ⟨1949720, by rfl⟩ : syracuseStep 2599627 = 3899441) B3899441
theorem B5851865 : Blo 1539967 5851865 := bstep (se 2 (by rfl) ⟨2194449, by rfl⟩ : syracuseStep 5851865 = 4388899) B4388899
theorem B2599769 : Blo 1539967 2599769 := bstep (se 2 (by rfl) ⟨974913, by rfl⟩ : syracuseStep 2599769 = 1949827) B1949827
theorem B3468185 : Blo 1539967 3468185 := bstep (se 2 (by rfl) ⟨1300569, by rfl⟩ : syracuseStep 3468185 = 2601139) B2601139
theorem B2599897 : Blo 1539967 2599897 := bstep (se 2 (by rfl) ⟨974961, by rfl⟩ : syracuseStep 2599897 = 1949923) B1949923
theorem B3468275 : Blo 1539967 3468275 := bstep (se 1 (by rfl) ⟨2601206, by rfl⟩ : syracuseStep 3468275 = 5202413) B5202413
theorem B57740309 : Blo 1539967 57740309 := bstep (se 6 (by rfl) ⟨1353288, by rfl⟩ : syracuseStep 57740309 = 2706577) B2706577
theorem B1805431 : Blo 1539967 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B8326475 : Blo 1539967 8326475 := bstep (se 1 (by rfl) ⟨6244856, by rfl⟩ : syracuseStep 8326475 = 12489713) B12489713
theorem B11103581 : Blo 1539967 11103581 := bstep (se 3 (by rfl) ⟨2081921, by rfl⟩ : syracuseStep 11103581 = 4163843) B4163843
theorem B7802243 : Blo 1539967 7802243 := bstep (se 1 (by rfl) ⟨5851682, by rfl⟩ : syracuseStep 7802243 = 11703365) B11703365
theorem B2600471 : Blo 1539967 2600471 := bstep (se 1 (by rfl) ⟨1950353, by rfl⟩ : syracuseStep 2600471 = 3900707) B3900707
theorem B2600599 : Blo 1539967 2600599 := bstep (se 1 (by rfl) ⟨1950449, by rfl⟩ : syracuseStep 2600599 = 3900899) B3900899
theorem B4165465 : Blo 1539967 4165465 := bstep (se 2 (by rfl) ⟨1562049, by rfl⟩ : syracuseStep 4165465 = 3124099) B3124099
theorem B5197661 : Blo 1539967 5197661 := bstep (se 3 (by rfl) ⟨974561, by rfl⟩ : syracuseStep 5197661 = 1949123) B1949123
theorem B1732567 : Blo 1539967 1732567 := bstep (se 1 (by rfl) ⟨1299425, by rfl⟩ : syracuseStep 1732567 = 2598851) B2598851
theorem B12496913 : Blo 1539967 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B6582323 : Blo 1539967 6582323 := bstep (se 1 (by rfl) ⟨4936742, by rfl⟩ : syracuseStep 6582323 = 9873485) B9873485
theorem B1732747 : Blo 1539967 1732747 := bstep (se 1 (by rfl) ⟨1299560, by rfl⟩ : syracuseStep 1732747 = 2599121) B2599121
theorem B3289241 : Blo 1539967 3289241 := bstep (se 2 (by rfl) ⟨1233465, by rfl⟩ : syracuseStep 3289241 = 2466931) B2466931
theorem B1732855 : Blo 1539967 1732855 := bstep (se 1 (by rfl) ⟨1299641, by rfl⟩ : syracuseStep 1732855 = 2599283) B2599283
theorem B49983749 : Blo 1539967 49983749 := bstep (se 4 (by rfl) ⟨4685976, by rfl⟩ : syracuseStep 49983749 = 9371953) B9371953
theorem B2601227 : Blo 1539967 2601227 := bstep (se 1 (by rfl) ⟨1950920, by rfl⟩ : syracuseStep 2601227 = 3901841) B3901841
theorem B4936025 : Blo 1539967 4936025 := bstep (se 2 (by rfl) ⟨1851009, by rfl⟩ : syracuseStep 4936025 = 3702019) B3702019
theorem B1733035 : Blo 1539967 1733035 := bstep (se 1 (by rfl) ⟨1299776, by rfl⟩ : syracuseStep 1733035 = 2599553) B2599553
theorem B11571635 : Blo 1539967 11571635 := bstep (se 1 (by rfl) ⟨8678726, by rfl⟩ : syracuseStep 11571635 = 17357453) B17357453
theorem B1733143 : Blo 1539967 1733143 := bstep (se 1 (by rfl) ⟨1299857, by rfl⟩ : syracuseStep 1733143 = 2599715) B2599715
theorem B13529693 : Blo 1539967 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B11752087 : Blo 1539967 11752087 := bstep (se 1 (by rfl) ⟨8814065, by rfl⟩ : syracuseStep 11752087 = 17628131) B17628131
theorem B1733323 : Blo 1539967 1733323 := bstep (se 1 (by rfl) ⟨1299992, by rfl⟩ : syracuseStep 1733323 = 2599985) B2599985
theorem B1733431 : Blo 1539967 1733431 := bstep (se 1 (by rfl) ⟨1300073, by rfl⟩ : syracuseStep 1733431 = 2600147) B2600147
theorem B40555363 : Blo 1539967 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B42169187 : Blo 1539967 42169187 := bstep (se 1 (by rfl) ⟨31626890, by rfl⟩ : syracuseStep 42169187 = 63253781) B63253781
theorem B17544113 : Blo 1539967 17544113 := bstep (se 2 (by rfl) ⟨6579042, by rfl⟩ : syracuseStep 17544113 = 13158085) B13158085
theorem B5198795 : Blo 1539967 5198795 := bstep (se 1 (by rfl) ⟨3899096, by rfl⟩ : syracuseStep 5198795 = 7798193) B7798193
theorem B1733611 : Blo 1539967 1733611 := bstep (se 1 (by rfl) ⟨1300208, by rfl⟩ : syracuseStep 1733611 = 2600417) B2600417
theorem B3609587 : Blo 1539967 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B1733719 : Blo 1539967 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B3290291 : Blo 1539967 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B4388033 : Blo 1539967 4388033 := bstep (se 2 (by rfl) ⟨1645512, by rfl⟩ : syracuseStep 4388033 = 3291025) B3291025
theorem B5199065 : Blo 1539967 5199065 := bstep (se 2 (by rfl) ⟨1949649, by rfl⟩ : syracuseStep 5199065 = 3899299) B3899299
theorem B4388057 : Blo 1539967 4388057 := bstep (se 2 (by rfl) ⟨1645521, by rfl⟩ : syracuseStep 4388057 = 3291043) B3291043
theorem B1733899 : Blo 1539967 1733899 := bstep (se 1 (by rfl) ⟨1300424, by rfl⟩ : syracuseStep 1733899 = 2600849) B2600849
theorem B1734007 : Blo 1539967 1734007 := bstep (se 1 (by rfl) ⟨1300505, by rfl⟩ : syracuseStep 1734007 = 2601011) B2601011
theorem B12490163 : Blo 1539967 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B3290881 : Blo 1539967 3290881 := bstep (se 2 (by rfl) ⟨1234080, by rfl⟩ : syracuseStep 3290881 = 2468161) B2468161
theorem B7796573 : Blo 1539967 7796573 := bstep (se 3 (by rfl) ⟨1461857, by rfl⟩ : syracuseStep 7796573 = 2923715) B2923715
theorem B5199767 : Blo 1539967 5199767 := bstep (se 1 (by rfl) ⟨3899825, by rfl⟩ : syracuseStep 5199767 = 7799651) B7799651
theorem B6584237 : Blo 1539967 6584237 := bstep (se 3 (by rfl) ⟨1234544, by rfl⟩ : syracuseStep 6584237 = 2469089) B2469089
theorem B2193419 : Blo 1539967 2193419 := bstep (se 1 (by rfl) ⟨1645064, by rfl⟩ : syracuseStep 2193419 = 3290129) B3290129
theorem B11704337 : Blo 1539967 11704337 := bstep (se 2 (by rfl) ⟨4389126, by rfl⟩ : syracuseStep 11704337 = 8778253) B8778253
theorem B5552221 : Blo 1539967 5552221 := bstep (se 3 (by rfl) ⟨1041041, by rfl⟩ : syracuseStep 5552221 = 2082083) B2082083
theorem B3512459 : Blo 1539967 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B1644791 : Blo 1539967 1644791 := bstep (se 1 (by rfl) ⟨1233593, by rfl⟩ : syracuseStep 1644791 = 2467187) B2467187
theorem B3512641 : Blo 1539967 3512641 := bstep (se 2 (by rfl) ⟨1317240, by rfl⟩ : syracuseStep 3512641 = 2634481) B2634481
theorem B11696561 : Blo 1539967 11696561 := bstep (se 2 (by rfl) ⟨4386210, by rfl⟩ : syracuseStep 11696561 = 8772421) B8772421
theorem B5200307 : Blo 1539967 5200307 := bstep (se 1 (by rfl) ⟨3900230, by rfl⟩ : syracuseStep 5200307 = 7800461) B7800461
theorem B4389299 : Blo 1539967 4389299 := bstep (se 1 (by rfl) ⟨3291974, by rfl⟩ : syracuseStep 4389299 = 6583949) B6583949
theorem B4938205 : Blo 1539967 4938205 := bstep (se 3 (by rfl) ⟨925913, by rfl⟩ : syracuseStep 4938205 = 1851827) B1851827
theorem B5200577 : Blo 1539967 5200577 := bstep (se 2 (by rfl) ⟨1950216, by rfl⟩ : syracuseStep 5200577 = 3900433) B3900433
theorem B6421265 : Blo 1539967 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B8444765 : Blo 1539967 8444765 := bstep (se 3 (by rfl) ⟨1583393, by rfl⟩ : syracuseStep 8444765 = 3166787) B3166787
theorem B11697047 : Blo 1539967 11697047 := bstep (se 1 (by rfl) ⟨8772785, by rfl⟩ : syracuseStep 11697047 = 17545571) B17545571
theorem B2194393 : Blo 1539967 2194393 := bstep (se 2 (by rfl) ⟨822897, by rfl⟩ : syracuseStep 2194393 = 1645795) B1645795
theorem B19004377 : Blo 1539967 19004377 := bstep (se 2 (by rfl) ⟨7126641, by rfl⟩ : syracuseStep 19004377 = 14253283) B14253283
theorem B5626955 : Blo 1539967 5626955 := bstep (se 1 (by rfl) ⟨4220216, by rfl⟩ : syracuseStep 5626955 = 8440433) B8440433
theorem B2923609 : Blo 1539967 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B5201117 : Blo 1539967 5201117 := bstep (se 3 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 5201117 = 1950419) B1950419
theorem B1850635 : Blo 1539967 1850635 := bstep (se 1 (by rfl) ⟨1387976, by rfl⟩ : syracuseStep 1850635 = 2775953) B2775953
theorem B3898955 : Blo 1539967 3898955 := bstep (se 1 (by rfl) ⟨2924216, by rfl⟩ : syracuseStep 3898955 = 5848433) B5848433
theorem B9870923 : Blo 1539967 9870923 := bstep (se 1 (by rfl) ⟨7403192, by rfl⟩ : syracuseStep 9870923 = 14806385) B14806385
theorem B2924171 : Blo 1539967 2924171 := bstep (se 1 (by rfl) ⟨2193128, by rfl⟩ : syracuseStep 2924171 = 4386257) B4386257
theorem B2965145 : Blo 1539967 2965145 := bstep (se 2 (by rfl) ⟨1111929, by rfl⟩ : syracuseStep 2965145 = 2223859) B2223859
theorem B19750661 : Blo 1539967 19750661 := bstep (se 4 (by rfl) ⟨1851624, by rfl⟩ : syracuseStep 19750661 = 3703249) B3703249
theorem B2776855 : Blo 1539967 2776855 := bstep (se 1 (by rfl) ⟨2082641, by rfl⟩ : syracuseStep 2776855 = 4165283) B4165283
theorem B2924353 : Blo 1539967 2924353 := bstep (se 2 (by rfl) ⟨1096632, by rfl⟩ : syracuseStep 2924353 = 2193265) B2193265
theorem B2309963 : Blo 1539967 2309963 := bstep (se 1 (by rfl) ⟨1732472, by rfl⟩ : syracuseStep 2309963 = 3464945) B3464945
theorem B3465035 : Blo 1539967 3465035 := bstep (se 1 (by rfl) ⟨2598776, by rfl⟩ : syracuseStep 3465035 = 5197553) B5197553
theorem B2309975 : Blo 1539967 2309975 := bstep (se 1 (by rfl) ⟨1732481, by rfl⟩ : syracuseStep 2309975 = 3464963) B3464963
theorem B3465089 : Blo 1539967 3465089 := bstep (se 2 (by rfl) ⟨1299408, by rfl⟩ : syracuseStep 3465089 = 2598817) B2598817
theorem B1539979 : Blo 1539967 1539979 := bstep (se 1 (by rfl) ⟨1154984, by rfl⟩ : syracuseStep 1539979 = 2309969) B2309969
theorem B1539991 : Blo 1539967 1539991 := bstep (se 1 (by rfl) ⟨1154993, by rfl⟩ : syracuseStep 1539991 = 2309987) B2309987
theorem B7798679 : Blo 1539967 7798679 := bstep (se 1 (by rfl) ⟨5849009, by rfl⟩ : syracuseStep 7798679 = 11698019) B11698019
theorem B2310041 : Blo 1539967 2310041 := bstep (se 2 (by rfl) ⟨866265, by rfl⟩ : syracuseStep 2310041 = 1732531) B1732531
theorem B1540011 : Blo 1539967 1540011 := bstep (se 1 (by rfl) ⟨1155008, by rfl⟩ : syracuseStep 1540011 = 2310017) B2310017
theorem B1540023 : Blo 1539967 1540023 := bstep (se 1 (by rfl) ⟨1155017, by rfl⟩ : syracuseStep 1540023 = 2310035) B2310035
theorem B1540043 : Blo 1539967 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B1540055 : Blo 1539967 1540055 := bstep (se 1 (by rfl) ⟨1155041, by rfl⟩ : syracuseStep 1540055 = 2310083) B2310083
theorem B1540075 : Blo 1539967 1540075 := bstep (se 1 (by rfl) ⟨1155056, by rfl⟩ : syracuseStep 1540075 = 2310113) B2310113
theorem B1540087 : Blo 1539967 1540087 := bstep (se 1 (by rfl) ⟨1155065, by rfl⟩ : syracuseStep 1540087 = 2310131) B2310131
theorem B1540103 : Blo 1539967 1540103 := bstep (se 1 (by rfl) ⟨1155077, by rfl⟩ : syracuseStep 1540103 = 2310155) B2310155
theorem B8331275 : Blo 1539967 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B1540111 : Blo 1539967 1540111 := bstep (se 1 (by rfl) ⟨1155083, by rfl⟩ : syracuseStep 1540111 = 2310167) B2310167
theorem B5849117 : Blo 1539967 5849117 := bstep (se 3 (by rfl) ⟨1096709, by rfl⟩ : syracuseStep 5849117 = 2193419) B2193419
theorem B5849131 : Blo 1539967 5849131 := bstep (se 1 (by rfl) ⟨4386848, by rfl⟩ : syracuseStep 5849131 = 8773697) B8773697
theorem B3702827 : Blo 1539967 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B2310203 : Blo 1539967 2310203 := bstep (se 1 (by rfl) ⟨1732652, by rfl⟩ : syracuseStep 2310203 = 3465305) B3465305
theorem B1540155 : Blo 1539967 1540155 := bstep (se 1 (by rfl) ⟨1155116, by rfl⟩ : syracuseStep 1540155 = 2310233) B2310233
theorem B5201981 : Blo 1539967 5201981 := bstep (se 3 (by rfl) ⟨975371, by rfl⟩ : syracuseStep 5201981 = 1950743) B1950743
theorem B2310263 : Blo 1539967 2310263 := bstep (se 1 (by rfl) ⟨1732697, by rfl⟩ : syracuseStep 2310263 = 3465395) B3465395
theorem B1540231 : Blo 1539967 1540231 := bstep (se 1 (by rfl) ⟨1155173, by rfl⟩ : syracuseStep 1540231 = 2310347) B2310347
theorem B2310287 : Blo 1539967 2310287 := bstep (se 1 (by rfl) ⟨1732715, by rfl⟩ : syracuseStep 2310287 = 3465431) B3465431
theorem B1540239 : Blo 1539967 1540239 := bstep (se 1 (by rfl) ⟨1155179, by rfl⟩ : syracuseStep 1540239 = 2310359) B2310359
theorem B2310329 : Blo 1539967 2310329 := bstep (se 2 (by rfl) ⟨866373, by rfl⟩ : syracuseStep 2310329 = 1732747) B1732747
theorem B1540283 : Blo 1539967 1540283 := bstep (se 1 (by rfl) ⟨1155212, by rfl⟩ : syracuseStep 1540283 = 2310425) B2310425
theorem B2310407 : Blo 1539967 2310407 := bstep (se 1 (by rfl) ⟨1732805, by rfl⟩ : syracuseStep 2310407 = 3465611) B3465611
theorem B1540359 : Blo 1539967 1540359 := bstep (se 1 (by rfl) ⟨1155269, by rfl⟩ : syracuseStep 1540359 = 2310539) B2310539
theorem B1540367 : Blo 1539967 1540367 := bstep (se 1 (by rfl) ⟨1155275, by rfl⟩ : syracuseStep 1540367 = 2310551) B2310551
theorem B2310443 : Blo 1539967 2310443 := bstep (se 1 (by rfl) ⟨1732832, by rfl⟩ : syracuseStep 2310443 = 3465665) B3465665
theorem B1540411 : Blo 1539967 1540411 := bstep (se 1 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 1540411 = 2310617) B2310617
theorem B2310473 : Blo 1539967 2310473 := bstep (se 2 (by rfl) ⟨866427, by rfl⟩ : syracuseStep 2310473 = 1732855) B1732855
theorem B3899735 : Blo 1539967 3899735 := bstep (se 1 (by rfl) ⟨2924801, by rfl⟩ : syracuseStep 3899735 = 5849603) B5849603
theorem B1540487 : Blo 1539967 1540487 := bstep (se 1 (by rfl) ⟨1155365, by rfl⟩ : syracuseStep 1540487 = 2310731) B2310731
theorem B1540495 : Blo 1539967 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B1950095 : Blo 1539967 1950095 := bstep (se 1 (by rfl) ⟨1462571, by rfl⟩ : syracuseStep 1950095 = 2925143) B2925143
theorem B6578617 : Blo 1539967 6578617 := bstep (se 2 (by rfl) ⟨2466981, by rfl⟩ : syracuseStep 6578617 = 4933963) B4933963
theorem B2310587 : Blo 1539967 2310587 := bstep (se 1 (by rfl) ⟨1732940, by rfl⟩ : syracuseStep 2310587 = 3465881) B3465881
theorem B1540539 : Blo 1539967 1540539 := bstep (se 1 (by rfl) ⟨1155404, by rfl⟩ : syracuseStep 1540539 = 2310809) B2310809
theorem B3703241 : Blo 1539967 3703241 := bstep (se 2 (by rfl) ⟨1388715, by rfl⟩ : syracuseStep 3703241 = 2777431) B2777431
theorem B2310647 : Blo 1539967 2310647 := bstep (se 1 (by rfl) ⟨1732985, by rfl⟩ : syracuseStep 2310647 = 3465971) B3465971
theorem B1540615 : Blo 1539967 1540615 := bstep (se 1 (by rfl) ⟨1155461, by rfl⟩ : syracuseStep 1540615 = 2310923) B2310923
theorem B2310671 : Blo 1539967 2310671 := bstep (se 1 (by rfl) ⟨1733003, by rfl⟩ : syracuseStep 2310671 = 3466007) B3466007
theorem B1540623 : Blo 1539967 1540623 := bstep (se 1 (by rfl) ⟨1155467, by rfl⟩ : syracuseStep 1540623 = 2310935) B2310935
theorem B3899947 : Blo 1539967 3899947 := bstep (se 1 (by rfl) ⟨2924960, by rfl⟩ : syracuseStep 3899947 = 5849921) B5849921
theorem B2310713 : Blo 1539967 2310713 := bstep (se 2 (by rfl) ⟨866517, by rfl⟩ : syracuseStep 2310713 = 1733035) B1733035
theorem B1540667 : Blo 1539967 1540667 := bstep (se 1 (by rfl) ⟨1155500, by rfl⟩ : syracuseStep 1540667 = 2311001) B2311001
theorem B14811767 : Blo 1539967 14811767 := bstep (se 1 (by rfl) ⟨11108825, by rfl⟩ : syracuseStep 14811767 = 22217651) B22217651
theorem B3465863 : Blo 1539967 3465863 := bstep (se 1 (by rfl) ⟨2599397, by rfl⟩ : syracuseStep 3465863 = 5198795) B5198795
theorem B2310791 : Blo 1539967 2310791 := bstep (se 1 (by rfl) ⟨1733093, by rfl⟩ : syracuseStep 2310791 = 3466187) B3466187
theorem B1540743 : Blo 1539967 1540743 := bstep (se 1 (by rfl) ⟨1155557, by rfl⟩ : syracuseStep 1540743 = 2311115) B2311115
theorem B1540751 : Blo 1539967 1540751 := bstep (se 1 (by rfl) ⟨1155563, by rfl⟩ : syracuseStep 1540751 = 2311127) B2311127
theorem B2310827 : Blo 1539967 2310827 := bstep (se 1 (by rfl) ⟨1733120, by rfl⟩ : syracuseStep 2310827 = 3466241) B3466241
theorem B3900089 : Blo 1539967 3900089 := bstep (se 2 (by rfl) ⟨1462533, by rfl⟩ : syracuseStep 3900089 = 2925067) B2925067
theorem B1540795 : Blo 1539967 1540795 := bstep (se 1 (by rfl) ⟨1155596, by rfl⟩ : syracuseStep 1540795 = 2311193) B2311193
theorem B7799489 : Blo 1539967 7799489 := bstep (se 2 (by rfl) ⟨2924808, by rfl⟩ : syracuseStep 7799489 = 5849617) B5849617
theorem B2310857 : Blo 1539967 2310857 := bstep (se 2 (by rfl) ⟨866571, by rfl⟩ : syracuseStep 2310857 = 1733143) B1733143
theorem B2081543 : Blo 1539967 2081543 := bstep (se 1 (by rfl) ⟨1561157, by rfl⟩ : syracuseStep 2081543 = 3122315) B3122315
theorem B1540871 : Blo 1539967 1540871 := bstep (se 1 (by rfl) ⟨1155653, by rfl⟩ : syracuseStep 1540871 = 2311307) B2311307
theorem B1540879 : Blo 1539967 1540879 := bstep (se 1 (by rfl) ⟨1155659, by rfl⟩ : syracuseStep 1540879 = 2311319) B2311319
theorem B15008561 : Blo 1539967 15008561 := bstep (se 2 (by rfl) ⟨5628210, by rfl⟩ : syracuseStep 15008561 = 11256421) B11256421
theorem B18998065 : Blo 1539967 18998065 := bstep (se 2 (by rfl) ⟨7124274, by rfl⟩ : syracuseStep 18998065 = 14248549) B14248549
theorem B3466043 : Blo 1539967 3466043 := bstep (se 1 (by rfl) ⟨2599532, by rfl⟩ : syracuseStep 3466043 = 5199065) B5199065
theorem B2310971 : Blo 1539967 2310971 := bstep (se 1 (by rfl) ⟨1733228, by rfl⟩ : syracuseStep 2310971 = 3466457) B3466457
theorem B1540923 : Blo 1539967 1540923 := bstep (se 1 (by rfl) ⟨1155692, by rfl⟩ : syracuseStep 1540923 = 2311385) B2311385
theorem B2925371 : Blo 1539967 2925371 := bstep (se 1 (by rfl) ⟨2194028, by rfl⟩ : syracuseStep 2925371 = 4388057) B4388057
theorem B2311031 : Blo 1539967 2311031 := bstep (se 1 (by rfl) ⟨1733273, by rfl⟩ : syracuseStep 2311031 = 3466547) B3466547
theorem B1540999 : Blo 1539967 1540999 := bstep (se 1 (by rfl) ⟨1155749, by rfl⟩ : syracuseStep 1540999 = 2311499) B2311499
theorem B2311055 : Blo 1539967 2311055 := bstep (se 1 (by rfl) ⟨1733291, by rfl⟩ : syracuseStep 2311055 = 3466583) B3466583
theorem B1541007 : Blo 1539967 1541007 := bstep (se 1 (by rfl) ⟨1155755, by rfl⟩ : syracuseStep 1541007 = 2311511) B2311511
theorem B3466169 : Blo 1539967 3466169 := bstep (se 2 (by rfl) ⟨1299813, by rfl⟩ : syracuseStep 3466169 = 2599627) B2599627
theorem B2311097 : Blo 1539967 2311097 := bstep (se 2 (by rfl) ⟨866661, by rfl⟩ : syracuseStep 2311097 = 1733323) B1733323
theorem B1541051 : Blo 1539967 1541051 := bstep (se 1 (by rfl) ⟨1155788, by rfl⟩ : syracuseStep 1541051 = 2311577) B2311577
theorem B2311175 : Blo 1539967 2311175 := bstep (se 1 (by rfl) ⟨1733381, by rfl⟩ : syracuseStep 2311175 = 3466763) B3466763
theorem B1541127 : Blo 1539967 1541127 := bstep (se 1 (by rfl) ⟨1155845, by rfl⟩ : syracuseStep 1541127 = 2311691) B2311691
theorem B1541135 : Blo 1539967 1541135 := bstep (se 1 (by rfl) ⟨1155851, by rfl⟩ : syracuseStep 1541135 = 2311703) B2311703
theorem B2311211 : Blo 1539967 2311211 := bstep (se 1 (by rfl) ⟨1733408, by rfl⟩ : syracuseStep 2311211 = 3466817) B3466817
theorem B1541179 : Blo 1539967 1541179 := bstep (se 1 (by rfl) ⟨1155884, by rfl⟩ : syracuseStep 1541179 = 2311769) B2311769
theorem B2311241 : Blo 1539967 2311241 := bstep (se 2 (by rfl) ⟨866715, by rfl⟩ : syracuseStep 2311241 = 1733431) B1733431
theorem B1541255 : Blo 1539967 1541255 := bstep (se 1 (by rfl) ⟨1155941, by rfl⟩ : syracuseStep 1541255 = 2311883) B2311883
theorem B1541263 : Blo 1539967 1541263 := bstep (se 1 (by rfl) ⟨1155947, by rfl⟩ : syracuseStep 1541263 = 2311895) B2311895
theorem B2311355 : Blo 1539967 2311355 := bstep (se 1 (by rfl) ⟨1733516, by rfl⟩ : syracuseStep 2311355 = 3467033) B3467033
theorem B1541307 : Blo 1539967 1541307 := bstep (se 1 (by rfl) ⟨1155980, by rfl⟩ : syracuseStep 1541307 = 2311961) B2311961
theorem B2311415 : Blo 1539967 2311415 := bstep (se 1 (by rfl) ⟨1733561, by rfl⟩ : syracuseStep 2311415 = 3467123) B3467123
theorem B1541383 : Blo 1539967 1541383 := bstep (se 1 (by rfl) ⟨1156037, by rfl⟩ : syracuseStep 1541383 = 2312075) B2312075
theorem B3466511 : Blo 1539967 3466511 := bstep (se 1 (by rfl) ⟨2599883, by rfl⟩ : syracuseStep 3466511 = 5199767) B5199767
theorem B2311439 : Blo 1539967 2311439 := bstep (se 1 (by rfl) ⟨1733579, by rfl⟩ : syracuseStep 2311439 = 3467159) B3467159
theorem B1541391 : Blo 1539967 1541391 := bstep (se 1 (by rfl) ⟨1156043, by rfl⟩ : syracuseStep 1541391 = 2312087) B2312087
theorem B3466529 : Blo 1539967 3466529 := bstep (se 2 (by rfl) ⟨1299948, by rfl⟩ : syracuseStep 3466529 = 2599897) B2599897
theorem B2925857 : Blo 1539967 2925857 := bstep (se 2 (by rfl) ⟨1097196, by rfl⟩ : syracuseStep 2925857 = 2194393) B2194393
theorem B25339169 : Blo 1539967 25339169 := bstep (se 2 (by rfl) ⟨9502188, by rfl⟩ : syracuseStep 25339169 = 19004377) B19004377
theorem B2311481 : Blo 1539967 2311481 := bstep (se 2 (by rfl) ⟨866805, by rfl⟩ : syracuseStep 2311481 = 1733611) B1733611
theorem B1541435 : Blo 1539967 1541435 := bstep (se 1 (by rfl) ⟨1156076, by rfl⟩ : syracuseStep 1541435 = 2312153) B2312153
theorem B2311559 : Blo 1539967 2311559 := bstep (se 1 (by rfl) ⟨1733669, by rfl⟩ : syracuseStep 2311559 = 3467339) B3467339
theorem B2311595 : Blo 1539967 2311595 := bstep (se 1 (by rfl) ⟨1733696, by rfl⟩ : syracuseStep 2311595 = 3467393) B3467393
theorem B2082235 : Blo 1539967 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B2311625 : Blo 1539967 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B2082295 : Blo 1539967 2082295 := bstep (se 1 (by rfl) ⟨1561721, by rfl⟩ : syracuseStep 2082295 = 3123443) B3123443
theorem B2311739 : Blo 1539967 2311739 := bstep (se 1 (by rfl) ⟨1733804, by rfl⟩ : syracuseStep 2311739 = 3467609) B3467609
theorem B36079181 : Blo 1539967 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B3466871 : Blo 1539967 3466871 := bstep (se 1 (by rfl) ⟨2600153, by rfl⟩ : syracuseStep 3466871 = 5200307) B5200307
theorem B2311799 : Blo 1539967 2311799 := bstep (se 1 (by rfl) ⟨1733849, by rfl⟩ : syracuseStep 2311799 = 3467699) B3467699
theorem B2926199 : Blo 1539967 2926199 := bstep (se 1 (by rfl) ⟨2194649, by rfl⟩ : syracuseStep 2926199 = 4389299) B4389299
theorem B2311823 : Blo 1539967 2311823 := bstep (se 1 (by rfl) ⟨1733867, by rfl⟩ : syracuseStep 2311823 = 3467735) B3467735
theorem B3901081 : Blo 1539967 3901081 := bstep (se 2 (by rfl) ⟨1462905, by rfl⟩ : syracuseStep 3901081 = 2925811) B2925811
theorem B2467513 : Blo 1539967 2467513 := bstep (se 2 (by rfl) ⟨925317, by rfl⟩ : syracuseStep 2467513 = 1850635) B1850635
theorem B2311865 : Blo 1539967 2311865 := bstep (se 2 (by rfl) ⟨866949, by rfl⟩ : syracuseStep 2311865 = 1733899) B1733899
theorem B7907053 : Blo 1539967 7907053 := bstep (se 3 (by rfl) ⟨1482572, by rfl⟩ : syracuseStep 7907053 = 2965145) B2965145
theorem B9373441 : Blo 1539967 9373441 := bstep (se 2 (by rfl) ⟨3515040, by rfl⟩ : syracuseStep 9373441 = 7030081) B7030081
theorem B2311943 : Blo 1539967 2311943 := bstep (se 1 (by rfl) ⟨1733957, by rfl⟩ : syracuseStep 2311943 = 3467915) B3467915
theorem B3467051 : Blo 1539967 3467051 := bstep (se 1 (by rfl) ⟨2600288, by rfl⟩ : syracuseStep 3467051 = 5200577) B5200577
theorem B2311979 : Blo 1539967 2311979 := bstep (se 1 (by rfl) ⟨1733984, by rfl⟩ : syracuseStep 2311979 = 3467969) B3467969
theorem B3901243 : Blo 1539967 3901243 := bstep (se 1 (by rfl) ⟨2925932, by rfl⟩ : syracuseStep 3901243 = 5851865) B5851865
theorem B2312009 : Blo 1539967 2312009 := bstep (se 2 (by rfl) ⟨867003, by rfl⟩ : syracuseStep 2312009 = 1734007) B1734007
theorem B5629843 : Blo 1539967 5629843 := bstep (se 1 (by rfl) ⟨4222382, by rfl⟩ : syracuseStep 5629843 = 8444765) B8444765
theorem B2312123 : Blo 1539967 2312123 := bstep (se 1 (by rfl) ⟨1734092, by rfl⟩ : syracuseStep 2312123 = 3468185) B3468185
theorem B3901385 : Blo 1539967 3901385 := bstep (se 2 (by rfl) ⟨1463019, by rfl⟩ : syracuseStep 3901385 = 2926039) B2926039
theorem B7800785 : Blo 1539967 7800785 := bstep (se 2 (by rfl) ⟨2925294, by rfl⟩ : syracuseStep 7800785 = 5850589) B5850589
theorem B2312183 : Blo 1539967 2312183 := bstep (se 1 (by rfl) ⟨1734137, by rfl⟩ : syracuseStep 2312183 = 3468275) B3468275
theorem B3467411 : Blo 1539967 3467411 := bstep (se 1 (by rfl) ⟨2600558, by rfl⟩ : syracuseStep 3467411 = 5201117) B5201117
theorem B3467465 : Blo 1539967 3467465 := bstep (se 2 (by rfl) ⟨1300299, by rfl⟩ : syracuseStep 3467465 = 2600599) B2600599
theorem B3901729 : Blo 1539967 3901729 := bstep (se 2 (by rfl) ⟨1463148, by rfl⟩ : syracuseStep 3901729 = 2926297) B2926297
theorem B2599303 : Blo 1539967 2599303 := bstep (se 1 (by rfl) ⟨1949477, by rfl⟩ : syracuseStep 2599303 = 3898955) B3898955
theorem B6580615 : Blo 1539967 6580615 := bstep (se 1 (by rfl) ⟨4935461, by rfl⟩ : syracuseStep 6580615 = 9870923) B9870923
theorem B13167107 : Blo 1539967 13167107 := bstep (se 1 (by rfl) ⟨9875330, by rfl⟩ : syracuseStep 13167107 = 19750661) B19750661
theorem B3468167 : Blo 1539967 3468167 := bstep (se 1 (by rfl) ⟨2601125, by rfl⟩ : syracuseStep 3468167 = 5202251) B5202251
theorem B2599951 : Blo 1539967 2599951 := bstep (se 1 (by rfl) ⟨1949963, by rfl⟩ : syracuseStep 2599951 = 3899927) B3899927
theorem B4385927 : Blo 1539967 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B11701421 : Blo 1539967 11701421 := bstep (se 3 (by rfl) ⟨2194016, by rfl⟩ : syracuseStep 11701421 = 4388033) B4388033
theorem B36547789 : Blo 1539967 36547789 := bstep (se 3 (by rfl) ⟨6852710, by rfl⟩ : syracuseStep 36547789 = 13705421) B13705421
theorem B4386109 : Blo 1539967 4386109 := bstep (se 3 (by rfl) ⟨822395, by rfl⟩ : syracuseStep 4386109 = 1644791) B1644791
theorem B7400963 : Blo 1539967 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B39497219 : Blo 1539967 39497219 := bstep (se 1 (by rfl) ⟨29622914, by rfl⟩ : syracuseStep 39497219 = 59245829) B59245829
theorem B9874973 : Blo 1539967 9874973 := bstep (se 3 (by rfl) ⟨1851557, by rfl⟩ : syracuseStep 9874973 = 3703115) B3703115
theorem B2600491 : Blo 1539967 2600491 := bstep (se 1 (by rfl) ⟨1950368, by rfl⟩ : syracuseStep 2600491 = 3900737) B3900737
theorem B8326775 : Blo 1539967 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B2600633 : Blo 1539967 2600633 := bstep (se 2 (by rfl) ⟨975237, by rfl⟩ : syracuseStep 2600633 = 1950475) B1950475
theorem B4386575 : Blo 1539967 4386575 := bstep (se 1 (by rfl) ⟨3289931, by rfl⟩ : syracuseStep 4386575 = 6579863) B6579863
theorem B1732495 : Blo 1539967 1732495 := bstep (se 1 (by rfl) ⟨1299371, by rfl⟩ : syracuseStep 1732495 = 2598743) B2598743
theorem B5197715 : Blo 1539967 5197715 := bstep (se 1 (by rfl) ⟨3898286, by rfl⟩ : syracuseStep 5197715 = 7796573) B7796573
theorem B42168215 : Blo 1539967 42168215 := bstep (se 1 (by rfl) ⟨31626161, by rfl⟩ : syracuseStep 42168215 = 63252323) B63252323
theorem B7802891 : Blo 1539967 7802891 := bstep (se 1 (by rfl) ⟨5852168, by rfl⟩ : syracuseStep 7802891 = 11704337) B11704337
theorem B7803053 : Blo 1539967 7803053 := bstep (se 3 (by rfl) ⟨1463072, by rfl⟩ : syracuseStep 7803053 = 2926145) B2926145
theorem B3289403 : Blo 1539967 3289403 := bstep (se 1 (by rfl) ⟨2467052, by rfl⟩ : syracuseStep 3289403 = 4934105) B4934105
theorem B1732999 : Blo 1539967 1732999 := bstep (se 1 (by rfl) ⟨1299749, by rfl⟩ : syracuseStep 1732999 = 2599499) B2599499
theorem B4280843 : Blo 1539967 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B1733179 : Blo 1539967 1733179 := bstep (se 1 (by rfl) ⟨1299884, by rfl⟩ : syracuseStep 1733179 = 2599769) B2599769
theorem B5550983 : Blo 1539967 5550983 := bstep (se 1 (by rfl) ⟨4163237, by rfl⟩ : syracuseStep 5550983 = 8326475) B8326475
theorem B7402387 : Blo 1539967 7402387 := bstep (se 1 (by rfl) ⟨5551790, by rfl⟩ : syracuseStep 7402387 = 11103581) B11103581
theorem B4387841 : Blo 1539967 4387841 := bstep (se 2 (by rfl) ⟨1645440, by rfl⟩ : syracuseStep 4387841 = 3290881) B3290881
theorem B1733647 : Blo 1539967 1733647 := bstep (se 1 (by rfl) ⟨1300235, by rfl⟩ : syracuseStep 1733647 = 2600471) B2600471
theorem B5199119 : Blo 1539967 5199119 := bstep (se 1 (by rfl) ⟨3899339, by rfl⟩ : syracuseStep 5199119 = 7798679) B7798679
theorem B8770963 : Blo 1539967 8770963 := bstep (se 1 (by rfl) ⟨6578222, by rfl⟩ : syracuseStep 8770963 = 13156445) B13156445
theorem B2635193 : Blo 1539967 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B2192827 : Blo 1539967 2192827 := bstep (se 1 (by rfl) ⟨1644620, by rfl⟩ : syracuseStep 2192827 = 3289241) B3289241
theorem B33306065 : Blo 1539967 33306065 := bstep (se 2 (by rfl) ⟨12489774, by rfl⟩ : syracuseStep 33306065 = 24979549) B24979549
theorem B7402961 : Blo 1539967 7402961 := bstep (se 2 (by rfl) ⟨2776110, by rfl⟩ : syracuseStep 7402961 = 5552221) B5552221
theorem B17552861 : Blo 1539967 17552861 := bstep (se 3 (by rfl) ⟨3291161, by rfl⟩ : syracuseStep 17552861 = 6582323) B6582323
theorem B33322499 : Blo 1539967 33322499 := bstep (se 1 (by rfl) ⟨24991874, by rfl⟩ : syracuseStep 33322499 = 49983749) B49983749
theorem B1734151 : Blo 1539967 1734151 := bstep (se 1 (by rfl) ⟨1300613, by rfl⟩ : syracuseStep 1734151 = 2601227) B2601227
theorem B15005213 : Blo 1539967 15005213 := bstep (se 3 (by rfl) ⟨2813477, by rfl⟩ : syracuseStep 15005213 = 5626955) B5626955
theorem B5199389 : Blo 1539967 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B11703851 : Blo 1539967 11703851 := bstep (se 1 (by rfl) ⟨8777888, by rfl⟩ : syracuseStep 11703851 = 17555777) B17555777
theorem B7714423 : Blo 1539967 7714423 := bstep (se 1 (by rfl) ⟨5785817, by rfl⟩ : syracuseStep 7714423 = 11571635) B11571635
theorem B2635465 : Blo 1539967 2635465 := bstep (se 2 (by rfl) ⟨988299, by rfl⟩ : syracuseStep 2635465 = 1976599) B1976599
theorem B4683521 : Blo 1539967 4683521 := bstep (se 2 (by rfl) ⟨1756320, by rfl⟩ : syracuseStep 4683521 = 3512641) B3512641
theorem B11696075 : Blo 1539967 11696075 := bstep (se 1 (by rfl) ⟨8772056, by rfl⟩ : syracuseStep 11696075 = 17544113) B17544113
theorem B6584273 : Blo 1539967 6584273 := bstep (se 2 (by rfl) ⟨2469102, by rfl⟩ : syracuseStep 6584273 = 4938205) B4938205
theorem B2406391 : Blo 1539967 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B2775073 : Blo 1539967 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B2193527 : Blo 1539967 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B15669449 : Blo 1539967 15669449 := bstep (se 2 (by rfl) ⟨5876043, by rfl⟩ : syracuseStep 15669449 = 11752087) B11752087
theorem B13162733 : Blo 1539967 13162733 := bstep (se 3 (by rfl) ⟨2468012, by rfl⟩ : syracuseStep 13162733 = 4936025) B4936025
theorem B54073817 : Blo 1539967 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B4389491 : Blo 1539967 4389491 := bstep (se 1 (by rfl) ⟨3292118, by rfl⟩ : syracuseStep 4389491 = 6584237) B6584237
theorem B2341639 : Blo 1539967 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B3898145 : Blo 1539967 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B2407241 : Blo 1539967 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B13163417 : Blo 1539967 13163417 := bstep (se 2 (by rfl) ⟨4936281, by rfl⟩ : syracuseStep 13163417 = 9872563) B9872563
theorem B5200793 : Blo 1539967 5200793 := bstep (se 2 (by rfl) ⟨1950297, by rfl⟩ : syracuseStep 5200793 = 3900595) B3900595
theorem B7797707 : Blo 1539967 7797707 := bstep (se 1 (by rfl) ⟨5848280, by rfl⟩ : syracuseStep 7797707 = 11696561) B11696561
theorem B8772695 : Blo 1539967 8772695 := bstep (se 1 (by rfl) ⟨6579521, by rfl⟩ : syracuseStep 8772695 = 13159043) B13159043
theorem B7798031 : Blo 1539967 7798031 := bstep (se 1 (by rfl) ⟨5848523, by rfl⟩ : syracuseStep 7798031 = 11697047) B11697047
theorem B38493539 : Blo 1539967 38493539 := bstep (se 1 (by rfl) ⟨28870154, by rfl⟩ : syracuseStep 38493539 = 57740309) B57740309
theorem B35569181 : Blo 1539967 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B5201495 : Blo 1539967 5201495 := bstep (se 1 (by rfl) ⟨3901121, by rfl⟩ : syracuseStep 5201495 = 7802243) B7802243
theorem B112451165 : Blo 1539967 112451165 := bstep (se 3 (by rfl) ⟨21084593, by rfl⟩ : syracuseStep 112451165 = 42169187) B42169187
theorem B3702473 : Blo 1539967 3702473 := bstep (se 2 (by rfl) ⟨1388427, by rfl⟩ : syracuseStep 3702473 = 2776855) B2776855
theorem B3899137 : Blo 1539967 3899137 := bstep (se 2 (by rfl) ⟨1462176, by rfl⟩ : syracuseStep 3899137 = 2924353) B2924353
theorem B1949447 : Blo 1539967 1949447 := bstep (se 1 (by rfl) ⟨1462085, by rfl⟩ : syracuseStep 1949447 = 2924171) B2924171
theorem B5553953 : Blo 1539967 5553953 := bstep (se 2 (by rfl) ⟨2082732, by rfl⟩ : syracuseStep 5553953 = 4165465) B4165465
theorem B1539975 : Blo 1539967 1539975 := bstep (se 1 (by rfl) ⟨1154981, by rfl⟩ : syracuseStep 1539975 = 2309963) B2309963
theorem B2310023 : Blo 1539967 2310023 := bstep (se 1 (by rfl) ⟨1732517, by rfl⟩ : syracuseStep 2310023 = 3465035) B3465035
theorem B1539983 : Blo 1539967 1539983 := bstep (se 1 (by rfl) ⟨1154987, by rfl⟩ : syracuseStep 1539983 = 2309975) B2309975
theorem B3465107 : Blo 1539967 3465107 := bstep (se 1 (by rfl) ⟨2598830, by rfl⟩ : syracuseStep 3465107 = 5197661) B5197661
theorem B2310059 : Blo 1539967 2310059 := bstep (se 1 (by rfl) ⟨1732544, by rfl⟩ : syracuseStep 2310059 = 3465089) B3465089
theorem B1540027 : Blo 1539967 1540027 := bstep (se 1 (by rfl) ⟨1155020, by rfl⟩ : syracuseStep 1540027 = 2310041) B2310041
theorem B2310089 : Blo 1539967 2310089 := bstep (se 2 (by rfl) ⟨866283, by rfl⟩ : syracuseStep 2310089 = 1732567) B1732567
theorem B3465161 : Blo 1539967 3465161 := bstep (se 2 (by rfl) ⟨1299435, by rfl⟩ : syracuseStep 3465161 = 2598871) B2598871
theorem B5554183 : Blo 1539967 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B5201927 : Blo 1539967 5201927 := bstep (se 1 (by rfl) ⟨3901445, by rfl⟩ : syracuseStep 5201927 = 7802891) B7802891
theorem B3899411 : Blo 1539967 3899411 := bstep (se 1 (by rfl) ⟨2924558, by rfl⟩ : syracuseStep 3899411 = 5849117) B5849117
theorem B1540135 : Blo 1539967 1540135 := bstep (se 1 (by rfl) ⟨1155101, by rfl⟩ : syracuseStep 1540135 = 2310203) B2310203
theorem B7798841 : Blo 1539967 7798841 := bstep (se 2 (by rfl) ⟨2924565, by rfl⟩ : syracuseStep 7798841 = 5849131) B5849131
theorem B1540175 : Blo 1539967 1540175 := bstep (se 1 (by rfl) ⟨1155131, by rfl⟩ : syracuseStep 1540175 = 2310263) B2310263
theorem B1540191 : Blo 1539967 1540191 := bstep (se 1 (by rfl) ⟨1155143, by rfl⟩ : syracuseStep 1540191 = 2310287) B2310287
theorem B5202035 : Blo 1539967 5202035 := bstep (se 1 (by rfl) ⟨3901526, by rfl⟩ : syracuseStep 5202035 = 7803053) B7803053
theorem B1540219 : Blo 1539967 1540219 := bstep (se 1 (by rfl) ⟨1155164, by rfl⟩ : syracuseStep 1540219 = 2310329) B2310329
theorem B1540271 : Blo 1539967 1540271 := bstep (se 1 (by rfl) ⟨1155203, by rfl⟩ : syracuseStep 1540271 = 2310407) B2310407
theorem B1540295 : Blo 1539967 1540295 := bstep (se 1 (by rfl) ⟨1155221, by rfl⟩ : syracuseStep 1540295 = 2310443) B2310443
theorem B1540315 : Blo 1539967 1540315 := bstep (se 1 (by rfl) ⟨1155236, by rfl⟩ : syracuseStep 1540315 = 2310473) B2310473
theorem B1540391 : Blo 1539967 1540391 := bstep (se 1 (by rfl) ⟨1155293, by rfl⟩ : syracuseStep 1540391 = 2310587) B2310587
theorem B5849405 : Blo 1539967 5849405 := bstep (se 3 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 5849405 = 2193527) B2193527
theorem B1540431 : Blo 1539967 1540431 := bstep (se 1 (by rfl) ⟨1155323, by rfl⟩ : syracuseStep 1540431 = 2310647) B2310647
theorem B1540447 : Blo 1539967 1540447 := bstep (se 1 (by rfl) ⟨1155335, by rfl⟩ : syracuseStep 1540447 = 2310671) B2310671
theorem B1540475 : Blo 1539967 1540475 := bstep (se 1 (by rfl) ⟨1155356, by rfl⟩ : syracuseStep 1540475 = 2310713) B2310713
theorem B5202305 : Blo 1539967 5202305 := bstep (se 2 (by rfl) ⟨1950864, by rfl⟩ : syracuseStep 5202305 = 3901729) B3901729
theorem B2310575 : Blo 1539967 2310575 := bstep (se 1 (by rfl) ⟨1732931, by rfl⟩ : syracuseStep 2310575 = 3465863) B3465863
theorem B1540527 : Blo 1539967 1540527 := bstep (se 1 (by rfl) ⟨1155395, by rfl⟩ : syracuseStep 1540527 = 2310791) B2310791
theorem B1540551 : Blo 1539967 1540551 := bstep (se 1 (by rfl) ⟨1155413, by rfl⟩ : syracuseStep 1540551 = 2310827) B2310827
theorem B1540571 : Blo 1539967 1540571 := bstep (se 1 (by rfl) ⟨1155428, by rfl⟩ : syracuseStep 1540571 = 2310857) B2310857
theorem B3465737 : Blo 1539967 3465737 := bstep (se 2 (by rfl) ⟨1299651, by rfl⟩ : syracuseStep 3465737 = 2599303) B2599303
theorem B2310665 : Blo 1539967 2310665 := bstep (se 2 (by rfl) ⟨866499, by rfl⟩ : syracuseStep 2310665 = 1732999) B1732999
theorem B8774153 : Blo 1539967 8774153 := bstep (se 2 (by rfl) ⟨3290307, by rfl⟩ : syracuseStep 8774153 = 6580615) B6580615
theorem B2310695 : Blo 1539967 2310695 := bstep (se 1 (by rfl) ⟨1733021, by rfl⟩ : syracuseStep 2310695 = 3466043) B3466043
theorem B1540647 : Blo 1539967 1540647 := bstep (se 1 (by rfl) ⟨1155485, by rfl⟩ : syracuseStep 1540647 = 2310971) B2310971
theorem B1950247 : Blo 1539967 1950247 := bstep (se 1 (by rfl) ⟨1462685, by rfl⟩ : syracuseStep 1950247 = 2925371) B2925371
theorem B1540687 : Blo 1539967 1540687 := bstep (se 1 (by rfl) ⟨1155515, by rfl⟩ : syracuseStep 1540687 = 2311031) B2311031
theorem B1540703 : Blo 1539967 1540703 := bstep (se 1 (by rfl) ⟨1155527, by rfl⟩ : syracuseStep 1540703 = 2311055) B2311055
theorem B2310779 : Blo 1539967 2310779 := bstep (se 1 (by rfl) ⟨1733084, by rfl⟩ : syracuseStep 2310779 = 3466169) B3466169
theorem B1540731 : Blo 1539967 1540731 := bstep (se 1 (by rfl) ⟨1155548, by rfl⟩ : syracuseStep 1540731 = 2311097) B2311097
theorem B2925227 : Blo 1539967 2925227 := bstep (se 1 (by rfl) ⟨2193920, by rfl⟩ : syracuseStep 2925227 = 4387841) B4387841
theorem B1540783 : Blo 1539967 1540783 := bstep (se 1 (by rfl) ⟨1155587, by rfl⟩ : syracuseStep 1540783 = 2311175) B2311175
theorem B1540807 : Blo 1539967 1540807 := bstep (se 1 (by rfl) ⟨1155605, by rfl⟩ : syracuseStep 1540807 = 2311211) B2311211
theorem B1540827 : Blo 1539967 1540827 := bstep (se 1 (by rfl) ⟨1155620, by rfl⟩ : syracuseStep 1540827 = 2311241) B2311241
theorem B2310905 : Blo 1539967 2310905 := bstep (se 2 (by rfl) ⟨866589, by rfl⟩ : syracuseStep 2310905 = 1733179) B1733179
theorem B1540903 : Blo 1539967 1540903 := bstep (se 1 (by rfl) ⟨1155677, by rfl⟩ : syracuseStep 1540903 = 2311355) B2311355
theorem B1540943 : Blo 1539967 1540943 := bstep (se 1 (by rfl) ⟨1155707, by rfl⟩ : syracuseStep 1540943 = 2311415) B2311415
theorem B3466079 : Blo 1539967 3466079 := bstep (se 1 (by rfl) ⟨2599559, by rfl⟩ : syracuseStep 3466079 = 5199119) B5199119
theorem B2311007 : Blo 1539967 2311007 := bstep (se 1 (by rfl) ⟨1733255, by rfl⟩ : syracuseStep 2311007 = 3466511) B3466511
theorem B1540959 : Blo 1539967 1540959 := bstep (se 1 (by rfl) ⟨1155719, by rfl⟩ : syracuseStep 1540959 = 2311439) B2311439
theorem B2311019 : Blo 1539967 2311019 := bstep (se 1 (by rfl) ⟨1733264, by rfl⟩ : syracuseStep 2311019 = 3466529) B3466529
theorem B1950571 : Blo 1539967 1950571 := bstep (se 1 (by rfl) ⟨1462928, by rfl⟩ : syracuseStep 1950571 = 2925857) B2925857
theorem B1540987 : Blo 1539967 1540987 := bstep (se 1 (by rfl) ⟨1155740, by rfl⟩ : syracuseStep 1540987 = 2311481) B2311481
theorem B1541039 : Blo 1539967 1541039 := bstep (se 1 (by rfl) ⟨1155779, by rfl⟩ : syracuseStep 1541039 = 2311559) B2311559
theorem B1541063 : Blo 1539967 1541063 := bstep (se 1 (by rfl) ⟨1155797, by rfl⟩ : syracuseStep 1541063 = 2311595) B2311595
theorem B1541083 : Blo 1539967 1541083 := bstep (se 1 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 1541083 = 2311625) B2311625
theorem B10003475 : Blo 1539967 10003475 := bstep (se 1 (by rfl) ⟨7502606, by rfl⟩ : syracuseStep 10003475 = 15005213) B15005213
theorem B3466259 : Blo 1539967 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B1541159 : Blo 1539967 1541159 := bstep (se 1 (by rfl) ⟨1155869, by rfl⟩ : syracuseStep 1541159 = 2311739) B2311739
theorem B24052787 : Blo 1539967 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B25330753 : Blo 1539967 25330753 := bstep (se 2 (by rfl) ⟨9499032, by rfl⟩ : syracuseStep 25330753 = 18998065) B18998065
theorem B2311247 : Blo 1539967 2311247 := bstep (se 1 (by rfl) ⟨1733435, by rfl⟩ : syracuseStep 2311247 = 3466871) B3466871
theorem B1541199 : Blo 1539967 1541199 := bstep (se 1 (by rfl) ⟨1155899, by rfl⟩ : syracuseStep 1541199 = 2311799) B2311799
theorem B1950799 : Blo 1539967 1950799 := bstep (se 1 (by rfl) ⟨1463099, by rfl⟩ : syracuseStep 1950799 = 2926199) B2926199
theorem B1541215 : Blo 1539967 1541215 := bstep (se 1 (by rfl) ⟨1155911, by rfl⟩ : syracuseStep 1541215 = 2311823) B2311823
theorem B1541243 : Blo 1539967 1541243 := bstep (se 1 (by rfl) ⟨1155932, by rfl⟩ : syracuseStep 1541243 = 2311865) B2311865
theorem B1541295 : Blo 1539967 1541295 := bstep (se 1 (by rfl) ⟨1155971, by rfl⟩ : syracuseStep 1541295 = 2311943) B2311943
theorem B2311367 : Blo 1539967 2311367 := bstep (se 1 (by rfl) ⟨1733525, by rfl⟩ : syracuseStep 2311367 = 3467051) B3467051
theorem B1541319 : Blo 1539967 1541319 := bstep (se 1 (by rfl) ⟨1155989, by rfl⟩ : syracuseStep 1541319 = 2311979) B2311979
theorem B1541339 : Blo 1539967 1541339 := bstep (se 1 (by rfl) ⟨1156004, by rfl⟩ : syracuseStep 1541339 = 2312009) B2312009
theorem B1541415 : Blo 1539967 1541415 := bstep (se 1 (by rfl) ⟨1156061, by rfl⟩ : syracuseStep 1541415 = 2312123) B2312123
theorem B1541455 : Blo 1539967 1541455 := bstep (se 1 (by rfl) ⟨1156091, by rfl⟩ : syracuseStep 1541455 = 2312183) B2312183
theorem B3466601 : Blo 1539967 3466601 := bstep (se 2 (by rfl) ⟨1299975, by rfl⟩ : syracuseStep 3466601 = 2599951) B2599951
theorem B2311529 : Blo 1539967 2311529 := bstep (se 2 (by rfl) ⟨866823, by rfl⟩ : syracuseStep 2311529 = 1733647) B1733647
theorem B2311607 : Blo 1539967 2311607 := bstep (se 1 (by rfl) ⟨1733705, by rfl⟩ : syracuseStep 2311607 = 3467411) B3467411
theorem B2311643 : Blo 1539967 2311643 := bstep (se 1 (by rfl) ⟨1733732, by rfl⟩ : syracuseStep 2311643 = 3467465) B3467465
theorem B10446299 : Blo 1539967 10446299 := bstep (se 1 (by rfl) ⟨7834724, by rfl⟩ : syracuseStep 10446299 = 15669449) B15669449
theorem B8775155 : Blo 1539967 8775155 := bstep (se 1 (by rfl) ⟨6581366, by rfl⟩ : syracuseStep 8775155 = 13162733) B13162733
theorem B2598763 : Blo 1539967 2598763 := bstep (se 1 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 2598763 = 3898145) B3898145
theorem B2312111 : Blo 1539967 2312111 := bstep (se 1 (by rfl) ⟨1734083, by rfl⟩ : syracuseStep 2312111 = 3468167) B3468167
theorem B8775611 : Blo 1539967 8775611 := bstep (se 1 (by rfl) ⟨6581708, by rfl⟩ : syracuseStep 8775611 = 13163417) B13163417
theorem B3467195 : Blo 1539967 3467195 := bstep (se 1 (by rfl) ⟨2600396, by rfl⟩ : syracuseStep 3467195 = 5200793) B5200793
theorem B2312201 : Blo 1539967 2312201 := bstep (se 2 (by rfl) ⟨867075, by rfl⟩ : syracuseStep 2312201 = 1734151) B1734151
theorem B3467321 : Blo 1539967 3467321 := bstep (se 2 (by rfl) ⟨1300245, by rfl⟩ : syracuseStep 3467321 = 2600491) B2600491
theorem B30025829 : Blo 1539967 30025829 := bstep (se 4 (by rfl) ⟨2814921, by rfl⟩ : syracuseStep 30025829 = 5629843) B5629843
theorem B7800947 : Blo 1539967 7800947 := bstep (se 1 (by rfl) ⟨5850710, by rfl⟩ : syracuseStep 7800947 = 11701421) B11701421
theorem B4933975 : Blo 1539967 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B26331479 : Blo 1539967 26331479 := bstep (se 1 (by rfl) ⟨19748609, by rfl⟩ : syracuseStep 26331479 = 39497219) B39497219
theorem B3467663 : Blo 1539967 3467663 := bstep (se 1 (by rfl) ⟨2600747, by rfl⟩ : syracuseStep 3467663 = 5201495) B5201495
theorem B74967443 : Blo 1539967 74967443 := bstep (se 1 (by rfl) ⟨56225582, by rfl⟩ : syracuseStep 74967443 = 112451165) B112451165
theorem B2468315 : Blo 1539967 2468315 := bstep (se 1 (by rfl) ⟨1851236, by rfl⟩ : syracuseStep 2468315 = 3702473) B3702473
theorem B2468551 : Blo 1539967 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B3467987 : Blo 1539967 3467987 := bstep (se 1 (by rfl) ⟨2600990, by rfl⟩ : syracuseStep 3467987 = 5201981) B5201981
theorem B2599823 : Blo 1539967 2599823 := bstep (se 1 (by rfl) ⟨1949867, by rfl⟩ : syracuseStep 2599823 = 3899735) B3899735
theorem B2468827 : Blo 1539967 2468827 := bstep (se 1 (by rfl) ⟨1851620, by rfl⟩ : syracuseStep 2468827 = 3703241) B3703241
theorem B2853895 : Blo 1539967 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B9874511 : Blo 1539967 9874511 := bstep (se 1 (by rfl) ⟨7405883, by rfl⟩ : syracuseStep 9874511 = 14811767) B14811767
theorem B2600059 : Blo 1539967 2600059 := bstep (se 1 (by rfl) ⟨1950044, by rfl⟩ : syracuseStep 2600059 = 3900089) B3900089
theorem B10005707 : Blo 1539967 10005707 := bstep (se 1 (by rfl) ⟨7504280, by rfl⟩ : syracuseStep 10005707 = 15008561) B15008561
theorem B67571117 : Blo 1539967 67571117 := bstep (se 3 (by rfl) ⟨12669584, by rfl⟩ : syracuseStep 67571117 = 25339169) B25339169
theorem B13160069 : Blo 1539967 13160069 := bstep (se 4 (by rfl) ⟨1233756, by rfl⟩ : syracuseStep 13160069 = 2467513) B2467513
theorem B22204043 : Blo 1539967 22204043 := bstep (se 1 (by rfl) ⟨16653032, by rfl⟩ : syracuseStep 22204043 = 33306065) B33306065
theorem B11701907 : Blo 1539967 11701907 := bstep (se 1 (by rfl) ⟨8776430, by rfl⟩ : syracuseStep 11701907 = 17552861) B17552861
theorem B7802567 : Blo 1539967 7802567 := bstep (se 1 (by rfl) ⟨5851925, by rfl⟩ : syracuseStep 7802567 = 11703851) B11703851
theorem B2600923 : Blo 1539967 2600923 := bstep (se 1 (by rfl) ⟨1950692, by rfl⟩ : syracuseStep 2600923 = 3901385) B3901385
theorem B12488741 : Blo 1539967 12488741 := bstep (se 4 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 12488741 = 2341639) B2341639
theorem B48730385 : Blo 1539967 48730385 := bstep (se 2 (by rfl) ⟨18273894, by rfl⟩ : syracuseStep 48730385 = 36547789) B36547789
theorem B36049211 : Blo 1539967 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B8778071 : Blo 1539967 8778071 := bstep (se 1 (by rfl) ⟨6583553, by rfl⟩ : syracuseStep 8778071 = 13167107) B13167107
theorem B11694617 : Blo 1539967 11694617 := bstep (se 2 (by rfl) ⟨4385481, by rfl⟩ : syracuseStep 11694617 = 8770963) B8770963
theorem B5198471 : Blo 1539967 5198471 := bstep (se 1 (by rfl) ⟨3898853, by rfl⟩ : syracuseStep 5198471 = 7797707) B7797707
theorem B12489389 : Blo 1539967 12489389 := bstep (se 3 (by rfl) ⟨2341760, by rfl⟩ : syracuseStep 12489389 = 4683521) B4683521
theorem B5550781 : Blo 1539967 5550781 := bstep (se 3 (by rfl) ⟨1040771, by rfl⟩ : syracuseStep 5550781 = 2081543) B2081543
theorem B5198525 : Blo 1539967 5198525 := bstep (se 3 (by rfl) ⟨974723, by rfl⟩ : syracuseStep 5198525 = 1949447) B1949447
theorem B10285897 : Blo 1539967 10285897 := bstep (se 2 (by rfl) ⟨3857211, by rfl⟩ : syracuseStep 10285897 = 7714423) B7714423
theorem B5198687 : Blo 1539967 5198687 := bstep (se 1 (by rfl) ⟨3899015, by rfl⟩ : syracuseStep 5198687 = 7798031) B7798031
theorem B25662359 : Blo 1539967 25662359 := bstep (se 1 (by rfl) ⟨19246769, by rfl⟩ : syracuseStep 25662359 = 38493539) B38493539
theorem B5198849 : Blo 1539967 5198849 := bstep (se 2 (by rfl) ⟨1949568, by rfl⟩ : syracuseStep 5198849 = 3899137) B3899137
theorem B12497921 : Blo 1539967 12497921 := bstep (se 2 (by rfl) ⟨4686720, by rfl⟩ : syracuseStep 12497921 = 9373441) B9373441
theorem B23712787 : Blo 1539967 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B6583315 : Blo 1539967 6583315 := bstep (se 1 (by rfl) ⟨4937486, by rfl⟩ : syracuseStep 6583315 = 9874973) B9874973
theorem B5551183 : Blo 1539967 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B1733755 : Blo 1539967 1733755 := bstep (se 1 (by rfl) ⟨1300316, by rfl⟩ : syracuseStep 1733755 = 2600633) B2600633
theorem B51336341 : Blo 1539967 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B28112143 : Blo 1539967 28112143 := bstep (se 1 (by rfl) ⟨21084107, by rfl⟩ : syracuseStep 28112143 = 42168215) B42168215
theorem B3700097 : Blo 1539967 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B2192935 : Blo 1539967 2192935 := bstep (se 1 (by rfl) ⟨1644701, by rfl⟩ : syracuseStep 2192935 = 3289403) B3289403
theorem B5199659 : Blo 1539967 5199659 := bstep (se 1 (by rfl) ⟨3899744, by rfl⟩ : syracuseStep 5199659 = 7799489) B7799489
theorem B8771489 : Blo 1539967 8771489 := bstep (se 2 (by rfl) ⟨3289308, by rfl⟩ : syracuseStep 8771489 = 6578617) B6578617
theorem B3700655 : Blo 1539967 3700655 := bstep (se 1 (by rfl) ⟨2775491, by rfl⟩ : syracuseStep 3700655 = 5550983) B5550983
theorem B5199929 : Blo 1539967 5199929 := bstep (se 2 (by rfl) ⟨1949973, by rfl⟩ : syracuseStep 5199929 = 3899947) B3899947
theorem B22214999 : Blo 1539967 22214999 := bstep (se 1 (by rfl) ⟨16661249, by rfl⟩ : syracuseStep 22214999 = 33322499) B33322499
theorem B5200253 : Blo 1539967 5200253 := bstep (se 3 (by rfl) ⟨975047, by rfl⟩ : syracuseStep 5200253 = 1950095) B1950095
theorem B7027181 : Blo 1539967 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B9869849 : Blo 1539967 9869849 := bstep (se 2 (by rfl) ⟨3701193, by rfl⟩ : syracuseStep 9869849 = 7402387) B7402387
theorem B19741229 : Blo 1539967 19741229 := bstep (se 3 (by rfl) ⟨3701480, by rfl⟩ : syracuseStep 19741229 = 7402961) B7402961
theorem B7797383 : Blo 1539967 7797383 := bstep (se 1 (by rfl) ⟨5848037, by rfl⟩ : syracuseStep 7797383 = 11696075) B11696075
theorem B5200523 : Blo 1539967 5200523 := bstep (se 1 (by rfl) ⟨3900392, by rfl⟩ : syracuseStep 5200523 = 7800785) B7800785
theorem B4389515 : Blo 1539967 4389515 := bstep (se 1 (by rfl) ⟨3292136, by rfl⟩ : syracuseStep 4389515 = 6584273) B6584273
theorem B11705309 : Blo 1539967 11705309 := bstep (se 3 (by rfl) ⟨2194745, by rfl⟩ : syracuseStep 11705309 = 4389491) B4389491
theorem B5848145 : Blo 1539967 5848145 := bstep (se 2 (by rfl) ⟨2193054, by rfl⟩ : syracuseStep 5848145 = 4386109) B4386109
theorem B1604827 : Blo 1539967 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B2923769 : Blo 1539967 2923769 := bstep (se 2 (by rfl) ⟨1096413, by rfl⟩ : syracuseStep 2923769 = 2192827) B2192827
theorem B2776313 : Blo 1539967 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B2776393 : Blo 1539967 2776393 := bstep (se 2 (by rfl) ⟨1041147, by rfl⟩ : syracuseStep 2776393 = 2082295) B2082295
theorem B11697533 : Blo 1539967 11697533 := bstep (se 3 (by rfl) ⟨2193287, by rfl⟩ : syracuseStep 11697533 = 4386575) B4386575
theorem B5848463 : Blo 1539967 5848463 := bstep (se 1 (by rfl) ⟨4386347, by rfl⟩ : syracuseStep 5848463 = 8772695) B8772695
theorem B2923951 : Blo 1539967 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B5201441 : Blo 1539967 5201441 := bstep (se 2 (by rfl) ⟨1950540, by rfl⟩ : syracuseStep 5201441 = 3901081) B3901081
theorem B3513953 : Blo 1539967 3513953 := bstep (se 2 (by rfl) ⟨1317732, by rfl⟩ : syracuseStep 3513953 = 2635465) B2635465
theorem B10542737 : Blo 1539967 10542737 := bstep (se 2 (by rfl) ⟨3953526, by rfl⟩ : syracuseStep 10542737 = 7907053) B7907053
theorem B5201657 : Blo 1539967 5201657 := bstep (se 2 (by rfl) ⟨1950621, by rfl⟩ : syracuseStep 5201657 = 3901243) B3901243
theorem B2309993 : Blo 1539967 2309993 := bstep (se 2 (by rfl) ⟨866247, by rfl⟩ : syracuseStep 2309993 = 1732495) B1732495
theorem B3702635 : Blo 1539967 3702635 := bstep (se 1 (by rfl) ⟨2776976, by rfl⟩ : syracuseStep 3702635 = 5553953) B5553953
theorem B1540015 : Blo 1539967 1540015 := bstep (se 1 (by rfl) ⟨1155011, by rfl⟩ : syracuseStep 1540015 = 2310023) B2310023
theorem B2310071 : Blo 1539967 2310071 := bstep (se 1 (by rfl) ⟨1732553, by rfl⟩ : syracuseStep 2310071 = 3465107) B3465107
theorem B3465143 : Blo 1539967 3465143 := bstep (se 1 (by rfl) ⟨2598857, by rfl⟩ : syracuseStep 3465143 = 5197715) B5197715
theorem B1540039 : Blo 1539967 1540039 := bstep (se 1 (by rfl) ⟨1155029, by rfl⟩ : syracuseStep 1540039 = 2310059) B2310059
theorem B1540059 : Blo 1539967 1540059 := bstep (se 1 (by rfl) ⟨1155044, by rfl⟩ : syracuseStep 1540059 = 2310089) B2310089
theorem B2310107 : Blo 1539967 2310107 := bstep (se 1 (by rfl) ⟨1732580, by rfl⟩ : syracuseStep 2310107 = 3465161) B3465161
theorem B7405577 : Blo 1539967 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B3899603 : Blo 1539967 3899603 := bstep (se 1 (by rfl) ⟨2924702, by rfl⟩ : syracuseStep 3899603 = 5849405) B5849405
theorem B1540383 : Blo 1539967 1540383 := bstep (se 1 (by rfl) ⟨1155287, by rfl⟩ : syracuseStep 1540383 = 2310575) B2310575
theorem B2310491 : Blo 1539967 2310491 := bstep (se 1 (by rfl) ⟨1732868, by rfl⟩ : syracuseStep 2310491 = 3465737) B3465737
theorem B1540443 : Blo 1539967 1540443 := bstep (se 1 (by rfl) ⟨1155332, by rfl⟩ : syracuseStep 1540443 = 2310665) B2310665
theorem B5849435 : Blo 1539967 5849435 := bstep (se 1 (by rfl) ⟨4387076, by rfl⟩ : syracuseStep 5849435 = 8774153) B8774153
theorem B1540463 : Blo 1539967 1540463 := bstep (se 1 (by rfl) ⟨1155347, by rfl⟩ : syracuseStep 1540463 = 2310695) B2310695
theorem B29606309 : Blo 1539967 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B1540519 : Blo 1539967 1540519 := bstep (se 1 (by rfl) ⟨1155389, by rfl⟩ : syracuseStep 1540519 = 2310779) B2310779
theorem B3465647 : Blo 1539967 3465647 := bstep (se 1 (by rfl) ⟨2599235, by rfl⟩ : syracuseStep 3465647 = 5198471) B5198471
theorem B6578633 : Blo 1539967 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B1950151 : Blo 1539967 1950151 := bstep (se 1 (by rfl) ⟨1462613, by rfl⟩ : syracuseStep 1950151 = 2925227) B2925227
theorem B3465683 : Blo 1539967 3465683 := bstep (se 1 (by rfl) ⟨2599262, by rfl⟩ : syracuseStep 3465683 = 5198525) B5198525
theorem B1540603 : Blo 1539967 1540603 := bstep (se 1 (by rfl) ⟨1155452, by rfl⟩ : syracuseStep 1540603 = 2310905) B2310905
theorem B3465791 : Blo 1539967 3465791 := bstep (se 1 (by rfl) ⟨2599343, by rfl⟩ : syracuseStep 3465791 = 5198687) B5198687
theorem B2310719 : Blo 1539967 2310719 := bstep (se 1 (by rfl) ⟨1733039, by rfl⟩ : syracuseStep 2310719 = 3466079) B3466079
theorem B1540671 : Blo 1539967 1540671 := bstep (se 1 (by rfl) ⟨1155503, by rfl⟩ : syracuseStep 1540671 = 2311007) B2311007
theorem B1540679 : Blo 1539967 1540679 := bstep (se 1 (by rfl) ⟨1155509, by rfl⟩ : syracuseStep 1540679 = 2311019) B2311019
theorem B3465899 : Blo 1539967 3465899 := bstep (se 1 (by rfl) ⟨2599424, by rfl⟩ : syracuseStep 3465899 = 5198849) B5198849
theorem B8331947 : Blo 1539967 8331947 := bstep (se 1 (by rfl) ⟨6248960, by rfl⟩ : syracuseStep 8331947 = 12497921) B12497921
theorem B6668983 : Blo 1539967 6668983 := bstep (se 1 (by rfl) ⟨5001737, by rfl⟩ : syracuseStep 6668983 = 10003475) B10003475
theorem B2310839 : Blo 1539967 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B1540831 : Blo 1539967 1540831 := bstep (se 1 (by rfl) ⟨1155623, by rfl⟩ : syracuseStep 1540831 = 2311247) B2311247
theorem B1540911 : Blo 1539967 1540911 := bstep (se 1 (by rfl) ⟨1155683, by rfl⟩ : syracuseStep 1540911 = 2311367) B2311367
theorem B2311067 : Blo 1539967 2311067 := bstep (se 1 (by rfl) ⟨1733300, by rfl⟩ : syracuseStep 2311067 = 3466601) B3466601
theorem B1541019 : Blo 1539967 1541019 := bstep (se 1 (by rfl) ⟨1155764, by rfl⟩ : syracuseStep 1541019 = 2311529) B2311529
theorem B2466731 : Blo 1539967 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B1541071 : Blo 1539967 1541071 := bstep (se 1 (by rfl) ⟨1155803, by rfl⟩ : syracuseStep 1541071 = 2311607) B2311607
theorem B1541095 : Blo 1539967 1541095 := bstep (se 1 (by rfl) ⟨1155821, by rfl⟩ : syracuseStep 1541095 = 2311643) B2311643
theorem B6964199 : Blo 1539967 6964199 := bstep (se 1 (by rfl) ⟨5223149, by rfl⟩ : syracuseStep 6964199 = 10446299) B10446299
theorem B5850103 : Blo 1539967 5850103 := bstep (se 1 (by rfl) ⟨4387577, by rfl⟩ : syracuseStep 5850103 = 8775155) B8775155
theorem B13714529 : Blo 1539967 13714529 := bstep (se 2 (by rfl) ⟨5142948, by rfl⟩ : syracuseStep 13714529 = 10285897) B10285897
theorem B3466439 : Blo 1539967 3466439 := bstep (se 1 (by rfl) ⟨2599829, by rfl⟩ : syracuseStep 3466439 = 5199659) B5199659
theorem B2467103 : Blo 1539967 2467103 := bstep (se 1 (by rfl) ⟨1850327, by rfl⟩ : syracuseStep 2467103 = 3700655) B3700655
theorem B1541407 : Blo 1539967 1541407 := bstep (se 1 (by rfl) ⟨1156055, by rfl⟩ : syracuseStep 1541407 = 2312111) B2312111
theorem B5850407 : Blo 1539967 5850407 := bstep (se 1 (by rfl) ⟨4387805, by rfl⟩ : syracuseStep 5850407 = 8775611) B8775611
theorem B2311463 : Blo 1539967 2311463 := bstep (se 1 (by rfl) ⟨1733597, by rfl⟩ : syracuseStep 2311463 = 3467195) B3467195
theorem B1541467 : Blo 1539967 1541467 := bstep (se 1 (by rfl) ⟨1156100, by rfl⟩ : syracuseStep 1541467 = 2312201) B2312201
theorem B3466619 : Blo 1539967 3466619 := bstep (se 1 (by rfl) ⟨2599964, by rfl⟩ : syracuseStep 3466619 = 5199929) B5199929
theorem B2311547 : Blo 1539967 2311547 := bstep (se 1 (by rfl) ⟨1733660, by rfl⟩ : syracuseStep 2311547 = 3467321) B3467321
theorem B3466745 : Blo 1539967 3466745 := bstep (se 2 (by rfl) ⟨1300029, by rfl⟩ : syracuseStep 3466745 = 2600059) B2600059
theorem B2311673 : Blo 1539967 2311673 := bstep (se 2 (by rfl) ⟨866877, by rfl⟩ : syracuseStep 2311673 = 1733755) B1733755
theorem B3466835 : Blo 1539967 3466835 := bstep (se 1 (by rfl) ⟨2600126, by rfl⟩ : syracuseStep 3466835 = 5200253) B5200253
theorem B2311775 : Blo 1539967 2311775 := bstep (se 1 (by rfl) ⟨1733831, by rfl⟩ : syracuseStep 2311775 = 3467663) B3467663
theorem B2139769 : Blo 1539967 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B6579899 : Blo 1539967 6579899 := bstep (se 1 (by rfl) ⟨4934924, by rfl⟩ : syracuseStep 6579899 = 9869849) B9869849
theorem B3467015 : Blo 1539967 3467015 := bstep (se 1 (by rfl) ⟨2600261, by rfl⟩ : syracuseStep 3467015 = 5200523) B5200523
theorem B2926343 : Blo 1539967 2926343 := bstep (se 1 (by rfl) ⟨2194757, by rfl⟩ : syracuseStep 2926343 = 4389515) B4389515
theorem B2311991 : Blo 1539967 2311991 := bstep (se 1 (by rfl) ⟨1733993, by rfl⟩ : syracuseStep 2311991 = 3467987) B3467987
theorem B6670471 : Blo 1539967 6670471 := bstep (se 1 (by rfl) ⟨5002853, by rfl⟩ : syracuseStep 6670471 = 10005707) B10005707
theorem B3467627 : Blo 1539967 3467627 := bstep (se 1 (by rfl) ⟨2600720, by rfl⟩ : syracuseStep 3467627 = 5201441) B5201441
theorem B7801271 : Blo 1539967 7801271 := bstep (se 1 (by rfl) ⟨5850953, by rfl⟩ : syracuseStep 7801271 = 11701907) B11701907
theorem B3467771 : Blo 1539967 3467771 := bstep (se 1 (by rfl) ⟨2600828, by rfl⟩ : syracuseStep 3467771 = 5201657) B5201657
theorem B2468423 : Blo 1539967 2468423 := bstep (se 1 (by rfl) ⟨1851317, by rfl⟩ : syracuseStep 2468423 = 3702635) B3702635
theorem B3467897 : Blo 1539967 3467897 := bstep (se 2 (by rfl) ⟨1300461, by rfl⟩ : syracuseStep 3467897 = 2600923) B2600923
theorem B3467951 : Blo 1539967 3467951 := bstep (se 1 (by rfl) ⟨2600963, by rfl⟩ : syracuseStep 3467951 = 5201927) B5201927
theorem B2599607 : Blo 1539967 2599607 := bstep (se 1 (by rfl) ⟨1949705, by rfl⟩ : syracuseStep 2599607 = 3899411) B3899411
theorem B8325827 : Blo 1539967 8325827 := bstep (se 1 (by rfl) ⟨6244370, by rfl⟩ : syracuseStep 8325827 = 12488741) B12488741
theorem B3468023 : Blo 1539967 3468023 := bstep (se 1 (by rfl) ⟨2601017, by rfl⟩ : syracuseStep 3468023 = 5202035) B5202035
theorem B5852047 : Blo 1539967 5852047 := bstep (se 1 (by rfl) ⟨4389035, by rfl⟩ : syracuseStep 5852047 = 8778071) B8778071
theorem B3468203 : Blo 1539967 3468203 := bstep (se 1 (by rfl) ⟨2601152, by rfl⟩ : syracuseStep 3468203 = 5202305) B5202305
theorem B8326259 : Blo 1539967 8326259 := bstep (se 1 (by rfl) ⟨6244694, by rfl⟩ : syracuseStep 8326259 = 12489389) B12489389
theorem B16035191 : Blo 1539967 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B2600329 : Blo 1539967 2600329 := bstep (se 2 (by rfl) ⟨975123, by rfl⟩ : syracuseStep 2600329 = 1950247) B1950247
theorem B7401041 : Blo 1539967 7401041 := bstep (se 2 (by rfl) ⟨2775390, by rfl⟩ : syracuseStep 7401041 = 5550781) B5550781
theorem B2600761 : Blo 1539967 2600761 := bstep (se 2 (by rfl) ⟨975285, by rfl⟩ : syracuseStep 2600761 = 1950571) B1950571
theorem B3805193 : Blo 1539967 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B31617049 : Blo 1539967 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B8777753 : Blo 1539967 8777753 := bstep (se 2 (by rfl) ⟨3291657, by rfl⟩ : syracuseStep 8777753 = 6583315) B6583315
theorem B20017219 : Blo 1539967 20017219 := bstep (se 1 (by rfl) ⟨15012914, by rfl⟩ : syracuseStep 20017219 = 30025829) B30025829
theorem B2601065 : Blo 1539967 2601065 := bstep (se 2 (by rfl) ⟨975399, by rfl⟩ : syracuseStep 2601065 = 1950799) B1950799
theorem B37482857 : Blo 1539967 37482857 := bstep (se 2 (by rfl) ⟨14056071, by rfl⟩ : syracuseStep 37482857 = 28112143) B28112143
theorem B13160819 : Blo 1539967 13160819 := bstep (se 1 (by rfl) ⟨9870614, by rfl⟩ : syracuseStep 13160819 = 19741229) B19741229
theorem B5198255 : Blo 1539967 5198255 := bstep (se 1 (by rfl) ⟨3898691, by rfl⟩ : syracuseStep 5198255 = 7797383) B7797383
theorem B1733215 : Blo 1539967 1733215 := bstep (se 1 (by rfl) ⟨1299911, by rfl⟩ : syracuseStep 1733215 = 2599823) B2599823
theorem B7803539 : Blo 1539967 7803539 := bstep (se 1 (by rfl) ⟨5852654, by rfl⟩ : syracuseStep 7803539 = 11705309) B11705309
theorem B6583007 : Blo 1539967 6583007 := bstep (se 1 (by rfl) ⟨4937255, by rfl⟩ : syracuseStep 6583007 = 9874511) B9874511
theorem B68432957 : Blo 1539967 68432957 := bstep (se 3 (by rfl) ⟨12831179, by rfl⟩ : syracuseStep 68432957 = 25662359) B25662359
theorem B5199227 : Blo 1539967 5199227 := bstep (se 1 (by rfl) ⟨3899420, by rfl⟩ : syracuseStep 5199227 = 7798841) B7798841
theorem B32486923 : Blo 1539967 32486923 := bstep (se 1 (by rfl) ⟨24365192, by rfl⟩ : syracuseStep 32486923 = 48730385) B48730385
theorem B24032807 : Blo 1539967 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B7796411 : Blo 1539967 7796411 := bstep (se 1 (by rfl) ⟨5847308, by rfl⟩ : syracuseStep 7796411 = 11694617) B11694617
theorem B7403501 : Blo 1539967 7403501 := bstep (se 3 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 7403501 = 2776313) B2776313
theorem B34224227 : Blo 1539967 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B3291401 : Blo 1539967 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B5847659 : Blo 1539967 5847659 := bstep (se 1 (by rfl) ⟨4385744, by rfl⟩ : syracuseStep 5847659 = 8771489) B8771489
theorem B3291769 : Blo 1539967 3291769 := bstep (se 2 (by rfl) ⟨1234413, by rfl⟩ : syracuseStep 3291769 = 2468827) B2468827
theorem B5200631 : Blo 1539967 5200631 := bstep (se 1 (by rfl) ⟨3900473, by rfl⟩ : syracuseStep 5200631 = 7800947) B7800947
theorem B33774337 : Blo 1539967 33774337 := bstep (se 2 (by rfl) ⟨12665376, by rfl⟩ : syracuseStep 33774337 = 25330753) B25330753
theorem B14809999 : Blo 1539967 14809999 := bstep (se 1 (by rfl) ⟨11107499, by rfl⟩ : syracuseStep 14809999 = 22214999) B22214999
theorem B17554319 : Blo 1539967 17554319 := bstep (se 1 (by rfl) ⟨13165739, by rfl⟩ : syracuseStep 17554319 = 26331479) B26331479
theorem B9370541 : Blo 1539967 9370541 := bstep (se 3 (by rfl) ⟨1756976, by rfl⟩ : syracuseStep 9370541 = 3513953) B3513953
theorem B49978295 : Blo 1539967 49978295 := bstep (se 1 (by rfl) ⟨37483721, by rfl⟩ : syracuseStep 49978295 = 74967443) B74967443
theorem B1645543 : Blo 1539967 1645543 := bstep (se 1 (by rfl) ⟨1234157, by rfl⟩ : syracuseStep 1645543 = 2468315) B2468315
theorem B4684787 : Blo 1539967 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B3701857 : Blo 1539967 3701857 := bstep (se 2 (by rfl) ⟨1388196, by rfl⟩ : syracuseStep 3701857 = 2776393) B2776393
theorem B3898601 : Blo 1539967 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B2923913 : Blo 1539967 2923913 := bstep (se 2 (by rfl) ⟨1096467, by rfl⟩ : syracuseStep 2923913 = 2192935) B2192935
theorem B3898763 : Blo 1539967 3898763 := bstep (se 1 (by rfl) ⟨2924072, by rfl⟩ : syracuseStep 3898763 = 5848145) B5848145
theorem B1949179 : Blo 1539967 1949179 := bstep (se 1 (by rfl) ⟨1461884, by rfl⟩ : syracuseStep 1949179 = 2923769) B2923769
theorem B7798355 : Blo 1539967 7798355 := bstep (se 1 (by rfl) ⟨5848766, by rfl⟩ : syracuseStep 7798355 = 11697533) B11697533
theorem B3898975 : Blo 1539967 3898975 := bstep (se 1 (by rfl) ⟨2924231, by rfl⟩ : syracuseStep 3898975 = 5848463) B5848463
theorem B45047411 : Blo 1539967 45047411 := bstep (se 1 (by rfl) ⟨33785558, by rfl⟩ : syracuseStep 45047411 = 67571117) B67571117
theorem B8773379 : Blo 1539967 8773379 := bstep (se 1 (by rfl) ⟨6580034, by rfl⟩ : syracuseStep 8773379 = 13160069) B13160069
theorem B14802695 : Blo 1539967 14802695 := bstep (se 1 (by rfl) ⟨11102021, by rfl⟩ : syracuseStep 14802695 = 22204043) B22204043
theorem B7028491 : Blo 1539967 7028491 := bstep (se 1 (by rfl) ⟨5271368, by rfl⟩ : syracuseStep 7028491 = 10542737) B10542737
theorem B5201711 : Blo 1539967 5201711 := bstep (se 1 (by rfl) ⟨3901283, by rfl⟩ : syracuseStep 5201711 = 7802567) B7802567
theorem B3465017 : Blo 1539967 3465017 := bstep (se 2 (by rfl) ⟨1299381, by rfl⟩ : syracuseStep 3465017 = 2598763) B2598763
theorem B1539995 : Blo 1539967 1539995 := bstep (se 1 (by rfl) ⟨1154996, by rfl⟩ : syracuseStep 1539995 = 2309993) B2309993
theorem B1540047 : Blo 1539967 1540047 := bstep (se 1 (by rfl) ⟨1155035, by rfl⟩ : syracuseStep 1540047 = 2310071) B2310071
theorem B2310095 : Blo 1539967 2310095 := bstep (se 1 (by rfl) ⟨1732571, by rfl⟩ : syracuseStep 2310095 = 3465143) B3465143
theorem B1540071 : Blo 1539967 1540071 := bstep (se 1 (by rfl) ⟨1155053, by rfl⟩ : syracuseStep 1540071 = 2310107) B2310107
theorem B42156065 : Blo 1539967 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B26689625 : Blo 1539967 26689625 := bstep (se 2 (by rfl) ⟨10008609, by rfl⟩ : syracuseStep 26689625 = 20017219) B20017219
theorem B1540327 : Blo 1539967 1540327 := bstep (se 1 (by rfl) ⟨1155245, by rfl⟩ : syracuseStep 1540327 = 2310491) B2310491
theorem B3899623 : Blo 1539967 3899623 := bstep (se 1 (by rfl) ⟨2924717, by rfl⟩ : syracuseStep 3899623 = 5849435) B5849435
theorem B8773879 : Blo 1539967 8773879 := bstep (se 1 (by rfl) ⟨6580409, by rfl⟩ : syracuseStep 8773879 = 13160819) B13160819
theorem B3465503 : Blo 1539967 3465503 := bstep (se 1 (by rfl) ⟨2599127, by rfl⟩ : syracuseStep 3465503 = 5198255) B5198255
theorem B2310431 : Blo 1539967 2310431 := bstep (se 1 (by rfl) ⟨1732823, by rfl⟩ : syracuseStep 2310431 = 3465647) B3465647
theorem B2310455 : Blo 1539967 2310455 := bstep (se 1 (by rfl) ⟨1732841, by rfl⟩ : syracuseStep 2310455 = 3465683) B3465683
theorem B2310527 : Blo 1539967 2310527 := bstep (se 1 (by rfl) ⟨1732895, by rfl⟩ : syracuseStep 2310527 = 3465791) B3465791
theorem B1540479 : Blo 1539967 1540479 := bstep (se 1 (by rfl) ⟨1155359, by rfl⟩ : syracuseStep 1540479 = 2310719) B2310719
theorem B5202359 : Blo 1539967 5202359 := bstep (se 1 (by rfl) ⟨3901769, by rfl⟩ : syracuseStep 5202359 = 7803539) B7803539
theorem B2310599 : Blo 1539967 2310599 := bstep (se 1 (by rfl) ⟨1732949, by rfl⟩ : syracuseStep 2310599 = 3465899) B3465899
theorem B5554631 : Blo 1539967 5554631 := bstep (se 1 (by rfl) ⟨4165973, by rfl⟩ : syracuseStep 5554631 = 8331947) B8331947
theorem B1540559 : Blo 1539967 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B1540711 : Blo 1539967 1540711 := bstep (se 1 (by rfl) ⟨1155533, by rfl⟩ : syracuseStep 1540711 = 2311067) B2311067
theorem B45621971 : Blo 1539967 45621971 := bstep (se 1 (by rfl) ⟨34216478, by rfl⟩ : syracuseStep 45621971 = 68432957) B68432957
theorem B6578941 : Blo 1539967 6578941 := bstep (se 3 (by rfl) ⟨1233551, by rfl⟩ : syracuseStep 6578941 = 2467103) B2467103
theorem B2310953 : Blo 1539967 2310953 := bstep (se 2 (by rfl) ⟨866607, by rfl⟩ : syracuseStep 2310953 = 1733215) B1733215
theorem B2310959 : Blo 1539967 2310959 := bstep (se 1 (by rfl) ⟨1733219, by rfl⟩ : syracuseStep 2310959 = 3466439) B3466439
theorem B3900271 : Blo 1539967 3900271 := bstep (se 1 (by rfl) ⟨2925203, by rfl⟩ : syracuseStep 3900271 = 5850407) B5850407
theorem B1540975 : Blo 1539967 1540975 := bstep (se 1 (by rfl) ⟨1155731, by rfl⟩ : syracuseStep 1540975 = 2311463) B2311463
theorem B3466151 : Blo 1539967 3466151 := bstep (se 1 (by rfl) ⟨2599613, by rfl⟩ : syracuseStep 3466151 = 5199227) B5199227
theorem B2311079 : Blo 1539967 2311079 := bstep (se 1 (by rfl) ⟨1733309, by rfl⟩ : syracuseStep 2311079 = 3466619) B3466619
theorem B1541031 : Blo 1539967 1541031 := bstep (se 1 (by rfl) ⟨1155773, by rfl⟩ : syracuseStep 1541031 = 2311547) B2311547
theorem B2311163 : Blo 1539967 2311163 := bstep (se 1 (by rfl) ⟨1733372, by rfl⟩ : syracuseStep 2311163 = 3466745) B3466745
theorem B1541115 : Blo 1539967 1541115 := bstep (se 1 (by rfl) ⟨1155836, by rfl⟩ : syracuseStep 1541115 = 2311673) B2311673
theorem B45032449 : Blo 1539967 45032449 := bstep (se 2 (by rfl) ⟨16887168, by rfl⟩ : syracuseStep 45032449 = 33774337) B33774337
theorem B2311223 : Blo 1539967 2311223 := bstep (se 1 (by rfl) ⟨1733417, by rfl⟩ : syracuseStep 2311223 = 3466835) B3466835
theorem B1541183 : Blo 1539967 1541183 := bstep (se 1 (by rfl) ⟨1155887, by rfl⟩ : syracuseStep 1541183 = 2311775) B2311775
theorem B2311343 : Blo 1539967 2311343 := bstep (se 1 (by rfl) ⟨1733507, by rfl⟩ : syracuseStep 2311343 = 3467015) B3467015
theorem B1950895 : Blo 1539967 1950895 := bstep (se 1 (by rfl) ⟨1463171, by rfl⟩ : syracuseStep 1950895 = 2926343) B2926343
theorem B1541327 : Blo 1539967 1541327 := bstep (se 1 (by rfl) ⟨1155995, by rfl⟩ : syracuseStep 1541327 = 2311991) B2311991
theorem B7800137 : Blo 1539967 7800137 := bstep (se 2 (by rfl) ⟨2925051, by rfl⟩ : syracuseStep 7800137 = 5850103) B5850103
theorem B22816151 : Blo 1539967 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B2311751 : Blo 1539967 2311751 := bstep (se 1 (by rfl) ⟨1733813, by rfl⟩ : syracuseStep 2311751 = 3467627) B3467627
theorem B2311847 : Blo 1539967 2311847 := bstep (se 1 (by rfl) ⟨1733885, by rfl⟩ : syracuseStep 2311847 = 3467771) B3467771
theorem B2311931 : Blo 1539967 2311931 := bstep (se 1 (by rfl) ⟨1733948, by rfl⟩ : syracuseStep 2311931 = 3467897) B3467897
theorem B2311967 : Blo 1539967 2311967 := bstep (se 1 (by rfl) ⟨1733975, by rfl⟩ : syracuseStep 2311967 = 3467951) B3467951
theorem B3467087 : Blo 1539967 3467087 := bstep (se 1 (by rfl) ⟨2600315, by rfl⟩ : syracuseStep 3467087 = 5200631) B5200631
theorem B2312015 : Blo 1539967 2312015 := bstep (se 1 (by rfl) ⟨1734011, by rfl⟩ : syracuseStep 2312015 = 3468023) B3468023
theorem B3467105 : Blo 1539967 3467105 := bstep (se 2 (by rfl) ⟨1300164, by rfl⟩ : syracuseStep 3467105 = 2600329) B2600329
theorem B2312135 : Blo 1539967 2312135 := bstep (se 1 (by rfl) ⟨1734101, by rfl⟩ : syracuseStep 2312135 = 3468203) B3468203
theorem B33318863 : Blo 1539967 33318863 := bstep (se 1 (by rfl) ⟨24989147, by rfl⟩ : syracuseStep 33318863 = 49978295) B49978295
theorem B3123191 : Blo 1539967 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B2598905 : Blo 1539967 2598905 := bstep (se 2 (by rfl) ⟨974589, by rfl⟩ : syracuseStep 2598905 = 1949179) B1949179
theorem B2599067 : Blo 1539967 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B2853025 : Blo 1539967 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B2599175 : Blo 1539967 2599175 := bstep (se 1 (by rfl) ⟨1949381, by rfl⟩ : syracuseStep 2599175 = 3898763) B3898763
theorem B4934027 : Blo 1539967 4934027 := bstep (se 1 (by rfl) ⟨3700520, by rfl⟩ : syracuseStep 4934027 = 7401041) B7401041
theorem B3467681 : Blo 1539967 3467681 := bstep (se 2 (by rfl) ⟨1300380, by rfl⟩ : syracuseStep 3467681 = 2600761) B2600761
theorem B3467807 : Blo 1539967 3467807 := bstep (se 1 (by rfl) ⟨2600855, by rfl⟩ : syracuseStep 3467807 = 5201711) B5201711
theorem B5851835 : Blo 1539967 5851835 := bstep (se 1 (by rfl) ⟨4388876, by rfl⟩ : syracuseStep 5851835 = 8777753) B8777753
theorem B2599735 : Blo 1539967 2599735 := bstep (se 1 (by rfl) ⟨1949801, by rfl⟩ : syracuseStep 2599735 = 3899603) B3899603
theorem B24988571 : Blo 1539967 24988571 := bstep (se 1 (by rfl) ⟨18741428, by rfl⟩ : syracuseStep 24988571 = 37482857) B37482857
theorem B36572077 : Blo 1539967 36572077 := bstep (se 3 (by rfl) ⟨6857264, by rfl⟩ : syracuseStep 36572077 = 13714529) B13714529
theorem B19737539 : Blo 1539967 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B4385755 : Blo 1539967 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B2600201 : Blo 1539967 2600201 := bstep (se 2 (by rfl) ⟨975075, by rfl⟩ : syracuseStep 2600201 = 1950151) B1950151
theorem B8777069 : Blo 1539967 8777069 := bstep (se 3 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 8777069 = 3291401) B3291401
theorem B8891977 : Blo 1539967 8891977 := bstep (se 2 (by rfl) ⟨3334491, by rfl⟩ : syracuseStep 8891977 = 6668983) B6668983
theorem B5197607 : Blo 1539967 5197607 := bstep (se 1 (by rfl) ⟨3898205, by rfl⟩ : syracuseStep 5197607 = 7796411) B7796411
theorem B4386599 : Blo 1539967 4386599 := bstep (se 1 (by rfl) ⟨3289949, by rfl⟩ : syracuseStep 4386599 = 6579899) B6579899
theorem B19746665 : Blo 1539967 19746665 := bstep (se 2 (by rfl) ⟨7404999, by rfl⟩ : syracuseStep 19746665 = 14809999) B14809999
theorem B7802729 : Blo 1539967 7802729 := bstep (se 2 (by rfl) ⟨2926023, by rfl⟩ : syracuseStep 7802729 = 5852047) B5852047
theorem B4935667 : Blo 1539967 4935667 := bstep (se 1 (by rfl) ⟨3701750, by rfl⟩ : syracuseStep 4935667 = 7403501) B7403501
theorem B4935809 : Blo 1539967 4935809 := bstep (se 2 (by rfl) ⟨1850928, by rfl⟩ : syracuseStep 4935809 = 3701857) B3701857
theorem B1733071 : Blo 1539967 1733071 := bstep (se 1 (by rfl) ⟨1299803, by rfl⟩ : syracuseStep 1733071 = 2599607) B2599607
theorem B5550551 : Blo 1539967 5550551 := bstep (se 1 (by rfl) ⟨4162913, by rfl⟩ : syracuseStep 5550551 = 8325827) B8325827
theorem B11702879 : Blo 1539967 11702879 := bstep (se 1 (by rfl) ⟨8777159, by rfl⟩ : syracuseStep 11702879 = 17554319) B17554319
theorem B6247027 : Blo 1539967 6247027 := bstep (se 1 (by rfl) ⟨4685270, by rfl⟩ : syracuseStep 6247027 = 9370541) B9370541
theorem B43315897 : Blo 1539967 43315897 := bstep (se 2 (by rfl) ⟨16243461, by rfl⟩ : syracuseStep 43315897 = 32486923) B32486923
theorem B5550839 : Blo 1539967 5550839 := bstep (se 1 (by rfl) ⟨4163129, by rfl⟩ : syracuseStep 5550839 = 8326259) B8326259
theorem B5198633 : Blo 1539967 5198633 := bstep (se 2 (by rfl) ⟨1949487, by rfl⟩ : syracuseStep 5198633 = 3898975) B3898975
theorem B5198903 : Blo 1539967 5198903 := bstep (se 1 (by rfl) ⟨3899177, by rfl⟩ : syracuseStep 5198903 = 7798355) B7798355
theorem B9868463 : Blo 1539967 9868463 := bstep (se 1 (by rfl) ⟨7401347, by rfl⟩ : syracuseStep 9868463 = 14802695) B14802695
theorem B4937051 : Blo 1539967 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B2536795 : Blo 1539967 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B1734043 : Blo 1539967 1734043 := bstep (se 1 (by rfl) ⟨1300532, by rfl⟩ : syracuseStep 1734043 = 2601065) B2601065
theorem B8893961 : Blo 1539967 8893961 := bstep (se 2 (by rfl) ⟨3335235, by rfl⟩ : syracuseStep 8893961 = 6670471) B6670471
theorem B4388671 : Blo 1539967 4388671 := bstep (se 1 (by rfl) ⟨3291503, by rfl⟩ : syracuseStep 4388671 = 6583007) B6583007
theorem B4389025 : Blo 1539967 4389025 := bstep (se 2 (by rfl) ⟨1645884, by rfl⟩ : syracuseStep 4389025 = 3291769) B3291769
theorem B16021871 : Blo 1539967 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B2194057 : Blo 1539967 2194057 := bstep (se 2 (by rfl) ⟨822771, by rfl⟩ : syracuseStep 2194057 = 1645543) B1645543
theorem B5200847 : Blo 1539967 5200847 := bstep (se 1 (by rfl) ⟨3900635, by rfl⟩ : syracuseStep 5200847 = 7801271) B7801271
theorem B1645615 : Blo 1539967 1645615 := bstep (se 1 (by rfl) ⟨1234211, by rfl⟩ : syracuseStep 1645615 = 2468423) B2468423
theorem B3898439 : Blo 1539967 3898439 := bstep (se 1 (by rfl) ⟨2923829, by rfl⟩ : syracuseStep 3898439 = 5847659) B5847659
theorem B10690127 : Blo 1539967 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B1949275 : Blo 1539967 1949275 := bstep (se 1 (by rfl) ⟨1461956, by rfl⟩ : syracuseStep 1949275 = 2923913) B2923913
theorem B9371321 : Blo 1539967 9371321 := bstep (se 2 (by rfl) ⟨3514245, by rfl⟩ : syracuseStep 9371321 = 7028491) B7028491
theorem B74284789 : Blo 1539967 74284789 := bstep (se 5 (by rfl) ⟨3482099, by rfl⟩ : syracuseStep 74284789 = 6964199) B6964199
theorem B30031607 : Blo 1539967 30031607 := bstep (se 1 (by rfl) ⟨22523705, by rfl⟩ : syracuseStep 30031607 = 45047411) B45047411
theorem B6577949 : Blo 1539967 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B5848919 : Blo 1539967 5848919 := bstep (se 1 (by rfl) ⟨4386689, by rfl⟩ : syracuseStep 5848919 = 8773379) B8773379
theorem B2310011 : Blo 1539967 2310011 := bstep (se 1 (by rfl) ⟨1732508, by rfl⟩ : syracuseStep 2310011 = 3465017) B3465017
theorem B1540063 : Blo 1539967 1540063 := bstep (se 1 (by rfl) ⟨1155047, by rfl⟩ : syracuseStep 1540063 = 2310095) B2310095
theorem B17793083 : Blo 1539967 17793083 := bstep (se 1 (by rfl) ⟨13344812, by rfl⟩ : syracuseStep 17793083 = 26689625) B26689625
theorem B2310335 : Blo 1539967 2310335 := bstep (se 1 (by rfl) ⟨1732751, by rfl⟩ : syracuseStep 2310335 = 3465503) B3465503
theorem B1540287 : Blo 1539967 1540287 := bstep (se 1 (by rfl) ⟨1155215, by rfl⟩ : syracuseStep 1540287 = 2310431) B2310431
theorem B1540303 : Blo 1539967 1540303 := bstep (se 1 (by rfl) ⟨1155227, by rfl⟩ : syracuseStep 1540303 = 2310455) B2310455
theorem B1540351 : Blo 1539967 1540351 := bstep (se 1 (by rfl) ⟨1155263, by rfl⟩ : syracuseStep 1540351 = 2310527) B2310527
theorem B1540399 : Blo 1539967 1540399 := bstep (se 1 (by rfl) ⟨1155299, by rfl⟩ : syracuseStep 1540399 = 2310599) B2310599
theorem B3703087 : Blo 1539967 3703087 := bstep (se 1 (by rfl) ⟨2777315, by rfl⟩ : syracuseStep 3703087 = 5554631) B5554631
theorem B11698505 : Blo 1539967 11698505 := bstep (se 2 (by rfl) ⟨4386939, by rfl⟩ : syracuseStep 11698505 = 8773879) B8773879
theorem B3465755 : Blo 1539967 3465755 := bstep (se 1 (by rfl) ⟨2599316, by rfl⟩ : syracuseStep 3465755 = 5198633) B5198633
theorem B1540635 : Blo 1539967 1540635 := bstep (se 1 (by rfl) ⟨1155476, by rfl⟩ : syracuseStep 1540635 = 2310953) B2310953
theorem B1540639 : Blo 1539967 1540639 := bstep (se 1 (by rfl) ⟨1155479, by rfl⟩ : syracuseStep 1540639 = 2310959) B2310959
theorem B33317477 : Blo 1539967 33317477 := bstep (se 4 (by rfl) ⟨3123513, by rfl⟩ : syracuseStep 33317477 = 6247027) B6247027
theorem B2310761 : Blo 1539967 2310761 := bstep (se 2 (by rfl) ⟨866535, by rfl⟩ : syracuseStep 2310761 = 1733071) B1733071
theorem B2310767 : Blo 1539967 2310767 := bstep (se 1 (by rfl) ⟨1733075, by rfl⟩ : syracuseStep 2310767 = 3466151) B3466151
theorem B1540719 : Blo 1539967 1540719 := bstep (se 1 (by rfl) ⟨1155539, by rfl⟩ : syracuseStep 1540719 = 2311079) B2311079
theorem B1540775 : Blo 1539967 1540775 := bstep (se 1 (by rfl) ⟨1155581, by rfl⟩ : syracuseStep 1540775 = 2311163) B2311163
theorem B3465935 : Blo 1539967 3465935 := bstep (se 1 (by rfl) ⟨2599451, by rfl⟩ : syracuseStep 3465935 = 5198903) B5198903
theorem B1540815 : Blo 1539967 1540815 := bstep (se 1 (by rfl) ⟨1155611, by rfl⟩ : syracuseStep 1540815 = 2311223) B2311223
theorem B6578975 : Blo 1539967 6578975 := bstep (se 1 (by rfl) ⟨4934231, by rfl⟩ : syracuseStep 6578975 = 9868463) B9868463
theorem B1540895 : Blo 1539967 1540895 := bstep (se 1 (by rfl) ⟨1155671, by rfl⟩ : syracuseStep 1540895 = 2311343) B2311343
theorem B2925409 : Blo 1539967 2925409 := bstep (se 2 (by rfl) ⟨1097028, by rfl⟩ : syracuseStep 2925409 = 2194057) B2194057
theorem B57754529 : Blo 1539967 57754529 := bstep (se 2 (by rfl) ⟨21657948, by rfl⟩ : syracuseStep 57754529 = 43315897) B43315897
theorem B1541167 : Blo 1539967 1541167 := bstep (se 1 (by rfl) ⟨1155875, by rfl⟩ : syracuseStep 1541167 = 2311751) B2311751
theorem B3466313 : Blo 1539967 3466313 := bstep (se 2 (by rfl) ⟨1299867, by rfl⟩ : syracuseStep 3466313 = 2599735) B2599735
theorem B1541231 : Blo 1539967 1541231 := bstep (se 1 (by rfl) ⟨1155923, by rfl⟩ : syracuseStep 1541231 = 2311847) B2311847
theorem B1541287 : Blo 1539967 1541287 := bstep (se 1 (by rfl) ⟨1155965, by rfl⟩ : syracuseStep 1541287 = 2311931) B2311931
theorem B1541311 : Blo 1539967 1541311 := bstep (se 1 (by rfl) ⟨1155983, by rfl⟩ : syracuseStep 1541311 = 2311967) B2311967
theorem B2311391 : Blo 1539967 2311391 := bstep (se 1 (by rfl) ⟨1733543, by rfl⟩ : syracuseStep 2311391 = 3467087) B3467087
theorem B1541343 : Blo 1539967 1541343 := bstep (se 1 (by rfl) ⟨1156007, by rfl⟩ : syracuseStep 1541343 = 2312015) B2312015
theorem B2311403 : Blo 1539967 2311403 := bstep (se 1 (by rfl) ⟨1733552, by rfl⟩ : syracuseStep 2311403 = 3467105) B3467105
theorem B1541423 : Blo 1539967 1541423 := bstep (se 1 (by rfl) ⟨1156067, by rfl⟩ : syracuseStep 1541423 = 2312135) B2312135
theorem B2082127 : Blo 1539967 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B2311787 : Blo 1539967 2311787 := bstep (se 1 (by rfl) ⟨1733840, by rfl⟩ : syracuseStep 2311787 = 3467681) B3467681
theorem B2311871 : Blo 1539967 2311871 := bstep (se 1 (by rfl) ⟨1733903, by rfl⟩ : syracuseStep 2311871 = 3467807) B3467807
theorem B3901223 : Blo 1539967 3901223 := bstep (se 1 (by rfl) ⟨2925917, by rfl⟩ : syracuseStep 3901223 = 5851835) B5851835
theorem B2312057 : Blo 1539967 2312057 := bstep (se 2 (by rfl) ⟨867021, by rfl⟩ : syracuseStep 2312057 = 1734043) B1734043
theorem B13158359 : Blo 1539967 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B3467231 : Blo 1539967 3467231 := bstep (se 1 (by rfl) ⟨2600423, by rfl⟩ : syracuseStep 3467231 = 5200847) B5200847
theorem B2598959 : Blo 1539967 2598959 := bstep (se 1 (by rfl) ⟨1949219, by rfl⟩ : syracuseStep 2598959 = 3898439) B3898439
theorem B17541197 : Blo 1539967 17541197 := bstep (se 3 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 17541197 = 6577949) B6577949
theorem B11855969 : Blo 1539967 11855969 := bstep (se 2 (by rfl) ⟨4445988, by rfl⟩ : syracuseStep 11855969 = 8891977) B8891977
theorem B2599033 : Blo 1539967 2599033 := bstep (se 2 (by rfl) ⟨974637, by rfl⟩ : syracuseStep 2599033 = 1949275) B1949275
theorem B5851379 : Blo 1539967 5851379 := bstep (se 1 (by rfl) ⟨4388534, by rfl⟩ : syracuseStep 5851379 = 8777069) B8777069
theorem B5851561 : Blo 1539967 5851561 := bstep (se 2 (by rfl) ⟨2194335, by rfl⟩ : syracuseStep 5851561 = 4388671) B4388671
theorem B6580889 : Blo 1539967 6580889 := bstep (se 2 (by rfl) ⟨2467833, by rfl⟩ : syracuseStep 6580889 = 4935667) B4935667
theorem B5852033 : Blo 1539967 5852033 := bstep (se 2 (by rfl) ⟨2194512, by rfl⟩ : syracuseStep 5852033 = 4389025) B4389025
theorem B8776613 : Blo 1539967 8776613 := bstep (se 4 (by rfl) ⟨822807, by rfl⟩ : syracuseStep 8776613 = 1645615) B1645615
theorem B3468239 : Blo 1539967 3468239 := bstep (se 1 (by rfl) ⟨2601179, by rfl⟩ : syracuseStep 3468239 = 5202359) B5202359
theorem B7801919 : Blo 1539967 7801919 := bstep (se 1 (by rfl) ⟨5851439, by rfl⟩ : syracuseStep 7801919 = 11702879) B11702879
theorem B15216133 : Blo 1539967 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B22212575 : Blo 1539967 22212575 := bstep (se 1 (by rfl) ⟨16659431, by rfl⟩ : syracuseStep 22212575 = 33318863) B33318863
theorem B1732603 : Blo 1539967 1732603 := bstep (se 1 (by rfl) ⟨1299452, by rfl⟩ : syracuseStep 1732603 = 2598905) B2598905
theorem B60043265 : Blo 1539967 60043265 := bstep (se 2 (by rfl) ⟨22516224, by rfl⟩ : syracuseStep 60043265 = 45032449) B45032449
theorem B1732711 : Blo 1539967 1732711 := bstep (se 1 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 1732711 = 2599067) B2599067
theorem B1732783 : Blo 1539967 1732783 := bstep (se 1 (by rfl) ⟨1299587, by rfl⟩ : syracuseStep 1732783 = 2599175) B2599175
theorem B2601193 : Blo 1539967 2601193 := bstep (se 2 (by rfl) ⟨975447, by rfl⟩ : syracuseStep 2601193 = 1950895) B1950895
theorem B3289351 : Blo 1539967 3289351 := bstep (se 1 (by rfl) ⟨2467013, by rfl⟩ : syracuseStep 3289351 = 4934027) B4934027
theorem B16659047 : Blo 1539967 16659047 := bstep (se 1 (by rfl) ⟨12494285, by rfl⟩ : syracuseStep 16659047 = 24988571) B24988571
theorem B1733467 : Blo 1539967 1733467 := bstep (se 1 (by rfl) ⟨1300100, by rfl⟩ : syracuseStep 1733467 = 2600201) B2600201
theorem B99046385 : Blo 1539967 99046385 := bstep (se 2 (by rfl) ⟨37142394, by rfl⟩ : syracuseStep 99046385 = 74284789) B74284789
theorem B6247547 : Blo 1539967 6247547 := bstep (se 1 (by rfl) ⟨4685660, by rfl⟩ : syracuseStep 6247547 = 9371321) B9371321
theorem B28104043 : Blo 1539967 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B3290539 : Blo 1539967 3290539 := bstep (se 1 (by rfl) ⟨2467904, by rfl⟩ : syracuseStep 3290539 = 4935809) B4935809
theorem B5199497 : Blo 1539967 5199497 := bstep (se 2 (by rfl) ⟨1949811, by rfl⟩ : syracuseStep 5199497 = 3899623) B3899623
theorem B3700367 : Blo 1539967 3700367 := bstep (se 1 (by rfl) ⟨2775275, by rfl⟩ : syracuseStep 3700367 = 5550551) B5550551
theorem B30414647 : Blo 1539967 30414647 := bstep (se 1 (by rfl) ⟨22810985, by rfl⟩ : syracuseStep 30414647 = 45621971) B45621971
theorem B3700559 : Blo 1539967 3700559 := bstep (se 1 (by rfl) ⟨2775419, by rfl⟩ : syracuseStep 3700559 = 5550839) B5550839
theorem B5200091 : Blo 1539967 5200091 := bstep (se 1 (by rfl) ⟨3900068, by rfl⟩ : syracuseStep 5200091 = 7800137) B7800137
theorem B3291367 : Blo 1539967 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B15210767 : Blo 1539967 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B8771921 : Blo 1539967 8771921 := bstep (se 2 (by rfl) ⟨3289470, by rfl⟩ : syracuseStep 8771921 = 6578941) B6578941
theorem B5929307 : Blo 1539967 5929307 := bstep (se 1 (by rfl) ⟨4446980, by rfl⟩ : syracuseStep 5929307 = 8893961) B8893961
theorem B5200361 : Blo 1539967 5200361 := bstep (se 2 (by rfl) ⟨1950135, by rfl⟩ : syracuseStep 5200361 = 3900271) B3900271
theorem B5847673 : Blo 1539967 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B10681247 : Blo 1539967 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B3382393 : Blo 1539967 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B80084285 : Blo 1539967 80084285 := bstep (se 3 (by rfl) ⟨15015803, by rfl⟩ : syracuseStep 80084285 = 30031607) B30031607
theorem B195051077 : Blo 1539967 195051077 := bstep (se 4 (by rfl) ⟨18286038, by rfl⟩ : syracuseStep 195051077 = 36572077) B36572077
theorem B7126751 : Blo 1539967 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B3465071 : Blo 1539967 3465071 := bstep (se 1 (by rfl) ⟨2598803, by rfl⟩ : syracuseStep 3465071 = 5197607) B5197607
theorem B2924399 : Blo 1539967 2924399 := bstep (se 1 (by rfl) ⟨2193299, by rfl⟩ : syracuseStep 2924399 = 4386599) B4386599
theorem B3899279 : Blo 1539967 3899279 := bstep (se 1 (by rfl) ⟨2924459, by rfl⟩ : syracuseStep 3899279 = 5848919) B5848919
theorem B13164443 : Blo 1539967 13164443 := bstep (se 1 (by rfl) ⟨9873332, by rfl⟩ : syracuseStep 13164443 = 19746665) B19746665
theorem B5201819 : Blo 1539967 5201819 := bstep (se 1 (by rfl) ⟨3901364, by rfl⟩ : syracuseStep 5201819 = 7802729) B7802729
theorem B1540007 : Blo 1539967 1540007 := bstep (se 1 (by rfl) ⟨1155005, by rfl⟩ : syracuseStep 1540007 = 2310011) B2310011
theorem B11862055 : Blo 1539967 11862055 := bstep (se 1 (by rfl) ⟨8896541, by rfl⟩ : syracuseStep 11862055 = 17793083) B17793083
theorem B1540223 : Blo 1539967 1540223 := bstep (se 1 (by rfl) ⟨1155167, by rfl⟩ : syracuseStep 1540223 = 2310335) B2310335
theorem B2310281 : Blo 1539967 2310281 := bstep (se 2 (by rfl) ⟨866355, by rfl⟩ : syracuseStep 2310281 = 1732711) B1732711
theorem B3465377 : Blo 1539967 3465377 := bstep (se 2 (by rfl) ⟨1299516, by rfl⟩ : syracuseStep 3465377 = 2599033) B2599033
theorem B7799003 : Blo 1539967 7799003 := bstep (se 1 (by rfl) ⟨5849252, by rfl⟩ : syracuseStep 7799003 = 11698505) B11698505
theorem B2310377 : Blo 1539967 2310377 := bstep (se 2 (by rfl) ⟨866391, by rfl⟩ : syracuseStep 2310377 = 1732783) B1732783
theorem B2310503 : Blo 1539967 2310503 := bstep (se 1 (by rfl) ⟨1732877, by rfl⟩ : syracuseStep 2310503 = 3465755) B3465755
theorem B1540507 : Blo 1539967 1540507 := bstep (se 1 (by rfl) ⟨1155380, by rfl⟩ : syracuseStep 1540507 = 2310761) B2310761
theorem B1540511 : Blo 1539967 1540511 := bstep (se 1 (by rfl) ⟨1155383, by rfl⟩ : syracuseStep 1540511 = 2310767) B2310767
theorem B2310623 : Blo 1539967 2310623 := bstep (se 1 (by rfl) ⟨1732967, by rfl⟩ : syracuseStep 2310623 = 3465935) B3465935
theorem B38503019 : Blo 1539967 38503019 := bstep (se 1 (by rfl) ⟨28877264, by rfl⟩ : syracuseStep 38503019 = 57754529) B57754529
theorem B2310875 : Blo 1539967 2310875 := bstep (se 1 (by rfl) ⟨1733156, by rfl⟩ : syracuseStep 2310875 = 3466313) B3466313
theorem B1540927 : Blo 1539967 1540927 := bstep (se 1 (by rfl) ⟨1155695, by rfl⟩ : syracuseStep 1540927 = 2311391) B2311391
theorem B1540935 : Blo 1539967 1540935 := bstep (se 1 (by rfl) ⟨1155701, by rfl⟩ : syracuseStep 1540935 = 2311403) B2311403
theorem B1541191 : Blo 1539967 1541191 := bstep (se 1 (by rfl) ⟨1155893, by rfl⟩ : syracuseStep 1541191 = 2311787) B2311787
theorem B3466331 : Blo 1539967 3466331 := bstep (se 1 (by rfl) ⟨2599748, by rfl⟩ : syracuseStep 3466331 = 5199497) B5199497
theorem B2466911 : Blo 1539967 2466911 := bstep (se 1 (by rfl) ⟨1850183, by rfl⟩ : syracuseStep 2466911 = 3700367) B3700367
theorem B2311289 : Blo 1539967 2311289 := bstep (se 2 (by rfl) ⟨866733, by rfl⟩ : syracuseStep 2311289 = 1733467) B1733467
theorem B3900545 : Blo 1539967 3900545 := bstep (se 2 (by rfl) ⟨1462704, by rfl⟩ : syracuseStep 3900545 = 2925409) B2925409
theorem B1541247 : Blo 1539967 1541247 := bstep (se 1 (by rfl) ⟨1155935, by rfl⟩ : syracuseStep 1541247 = 2311871) B2311871
theorem B2467039 : Blo 1539967 2467039 := bstep (se 1 (by rfl) ⟨1850279, by rfl⟩ : syracuseStep 2467039 = 3700559) B3700559
theorem B1541371 : Blo 1539967 1541371 := bstep (se 1 (by rfl) ⟨1156028, by rfl⟩ : syracuseStep 1541371 = 2312057) B2312057
theorem B2311487 : Blo 1539967 2311487 := bstep (se 1 (by rfl) ⟨1733615, by rfl⟩ : syracuseStep 2311487 = 3467231) B3467231
theorem B3466727 : Blo 1539967 3466727 := bstep (se 1 (by rfl) ⟨2600045, by rfl⟩ : syracuseStep 3466727 = 5200091) B5200091
theorem B3900919 : Blo 1539967 3900919 := bstep (se 1 (by rfl) ⟨2925689, by rfl⟩ : syracuseStep 3900919 = 5851379) B5851379
theorem B3466907 : Blo 1539967 3466907 := bstep (se 1 (by rfl) ⟨2600180, by rfl⟩ : syracuseStep 3466907 = 5200361) B5200361
theorem B37472057 : Blo 1539967 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B3901355 : Blo 1539967 3901355 := bstep (se 1 (by rfl) ⟨2926016, by rfl⟩ : syracuseStep 3901355 = 5852033) B5852033
theorem B7120831 : Blo 1539967 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B5851075 : Blo 1539967 5851075 := bstep (se 1 (by rfl) ⟨4388306, by rfl⟩ : syracuseStep 5851075 = 8776613) B8776613
theorem B2312159 : Blo 1539967 2312159 := bstep (se 1 (by rfl) ⟨1734119, by rfl⟩ : syracuseStep 2312159 = 3468239) B3468239
theorem B53389523 : Blo 1539967 53389523 := bstep (se 1 (by rfl) ⟨40042142, by rfl⟩ : syracuseStep 53389523 = 80084285) B80084285
theorem B130034051 : Blo 1539967 130034051 := bstep (se 1 (by rfl) ⟨97525538, by rfl⟩ : syracuseStep 130034051 = 195051077) B195051077
theorem B2599519 : Blo 1539967 2599519 := bstep (se 1 (by rfl) ⟨1949639, by rfl⟩ : syracuseStep 2599519 = 3899279) B3899279
theorem B8776295 : Blo 1539967 8776295 := bstep (se 1 (by rfl) ⟨6582221, by rfl⟩ : syracuseStep 8776295 = 13164443) B13164443
theorem B3467879 : Blo 1539967 3467879 := bstep (se 1 (by rfl) ⟨2600909, by rfl⟩ : syracuseStep 3467879 = 5201819) B5201819
theorem B40028843 : Blo 1539967 40028843 := bstep (se 1 (by rfl) ⟨30021632, by rfl⟩ : syracuseStep 40028843 = 60043265) B60043265
theorem B3468257 : Blo 1539967 3468257 := bstep (se 2 (by rfl) ⟨1300596, by rfl⟩ : syracuseStep 3468257 = 2601193) B2601193
theorem B4385801 : Blo 1539967 4385801 := bstep (se 2 (by rfl) ⟨1644675, by rfl⟩ : syracuseStep 4385801 = 3289351) B3289351
theorem B22211651 : Blo 1539967 22211651 := bstep (se 1 (by rfl) ⟨16658738, by rfl⟩ : syracuseStep 22211651 = 33317477) B33317477
theorem B4385983 : Blo 1539967 4385983 := bstep (se 1 (by rfl) ⟨3289487, by rfl⟩ : syracuseStep 4385983 = 6578975) B6578975
theorem B7802081 : Blo 1539967 7802081 := bstep (se 2 (by rfl) ⟨2925780, by rfl⟩ : syracuseStep 7802081 = 5851561) B5851561
theorem B66030923 : Blo 1539967 66030923 := bstep (se 1 (by rfl) ⟨49523192, by rfl⟩ : syracuseStep 66030923 = 99046385) B99046385
theorem B40562045 : Blo 1539967 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B4165031 : Blo 1539967 4165031 := bstep (se 1 (by rfl) ⟨3123773, by rfl⟩ : syracuseStep 4165031 = 6247547) B6247547
theorem B2600815 : Blo 1539967 2600815 := bstep (se 1 (by rfl) ⟨1950611, by rfl⟩ : syracuseStep 2600815 = 3901223) B3901223
theorem B1732639 : Blo 1539967 1732639 := bstep (se 1 (by rfl) ⟨1299479, by rfl⟩ : syracuseStep 1732639 = 2598959) B2598959
theorem B11694131 : Blo 1539967 11694131 := bstep (se 1 (by rfl) ⟨8770598, by rfl⟩ : syracuseStep 11694131 = 17541197) B17541197
theorem B4509857 : Blo 1539967 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B3952871 : Blo 1539967 3952871 := bstep (se 1 (by rfl) ⟨2964653, by rfl⟩ : syracuseStep 3952871 = 5929307) B5929307
theorem B4387259 : Blo 1539967 4387259 := bstep (se 1 (by rfl) ⟨3290444, by rfl⟩ : syracuseStep 4387259 = 6580889) B6580889
theorem B4387385 : Blo 1539967 4387385 := bstep (se 2 (by rfl) ⟨1645269, by rfl⟩ : syracuseStep 4387385 = 3290539) B3290539
theorem B20288177 : Blo 1539967 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B81105725 : Blo 1539967 81105725 := bstep (se 3 (by rfl) ⟨15207323, by rfl⟩ : syracuseStep 81105725 = 30414647) B30414647
theorem B14808383 : Blo 1539967 14808383 := bstep (se 1 (by rfl) ⟨11106287, by rfl⟩ : syracuseStep 14808383 = 22212575) B22212575
theorem B4388489 : Blo 1539967 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B4937449 : Blo 1539967 4937449 := bstep (se 2 (by rfl) ⟨1851543, by rfl⟩ : syracuseStep 4937449 = 3703087) B3703087
theorem B11106031 : Blo 1539967 11106031 := bstep (se 1 (by rfl) ⟨8329523, by rfl⟩ : syracuseStep 11106031 = 16659047) B16659047
theorem B7796897 : Blo 1539967 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B8772239 : Blo 1539967 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B7903979 : Blo 1539967 7903979 := bstep (se 1 (by rfl) ⟨5927984, by rfl⟩ : syracuseStep 7903979 = 11855969) B11855969
theorem B5847947 : Blo 1539967 5847947 := bstep (se 1 (by rfl) ⟨4385960, by rfl⟩ : syracuseStep 5847947 = 8771921) B8771921
theorem B2776169 : Blo 1539967 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B19004669 : Blo 1539967 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B5201279 : Blo 1539967 5201279 := bstep (se 1 (by rfl) ⟨3900959, by rfl⟩ : syracuseStep 5201279 = 7801919) B7801919
theorem B1949599 : Blo 1539967 1949599 := bstep (se 1 (by rfl) ⟨1462199, by rfl⟩ : syracuseStep 1949599 = 2924399) B2924399
theorem B2310047 : Blo 1539967 2310047 := bstep (se 1 (by rfl) ⟨1732535, by rfl⟩ : syracuseStep 2310047 = 3465071) B3465071
theorem B2310137 : Blo 1539967 2310137 := bstep (se 2 (by rfl) ⟨866301, by rfl⟩ : syracuseStep 2310137 = 1732603) B1732603
theorem B2310185 : Blo 1539967 2310185 := bstep (se 2 (by rfl) ⟨866319, by rfl⟩ : syracuseStep 2310185 = 1732639) B1732639
theorem B1540187 : Blo 1539967 1540187 := bstep (se 1 (by rfl) ⟨1155140, by rfl⟩ : syracuseStep 1540187 = 2310281) B2310281
theorem B2310251 : Blo 1539967 2310251 := bstep (se 1 (by rfl) ⟨1732688, by rfl⟩ : syracuseStep 2310251 = 3465377) B3465377
theorem B1540251 : Blo 1539967 1540251 := bstep (se 1 (by rfl) ⟨1155188, by rfl⟩ : syracuseStep 1540251 = 2310377) B2310377
theorem B1540335 : Blo 1539967 1540335 := bstep (se 1 (by rfl) ⟨1155251, by rfl⟩ : syracuseStep 1540335 = 2310503) B2310503
theorem B2924839 : Blo 1539967 2924839 := bstep (se 1 (by rfl) ⟨2193629, by rfl⟩ : syracuseStep 2924839 = 4387259) B4387259
theorem B1540415 : Blo 1539967 1540415 := bstep (se 1 (by rfl) ⟨1155311, by rfl⟩ : syracuseStep 1540415 = 2310623) B2310623
theorem B2924923 : Blo 1539967 2924923 := bstep (se 1 (by rfl) ⟨2193692, by rfl⟩ : syracuseStep 2924923 = 4387385) B4387385
theorem B13525451 : Blo 1539967 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B1540583 : Blo 1539967 1540583 := bstep (se 1 (by rfl) ⟨1155437, by rfl⟩ : syracuseStep 1540583 = 2310875) B2310875
theorem B2310887 : Blo 1539967 2310887 := bstep (se 1 (by rfl) ⟨1733165, by rfl⟩ : syracuseStep 2310887 = 3466331) B3466331
theorem B1540859 : Blo 1539967 1540859 := bstep (se 1 (by rfl) ⟨1155644, by rfl⟩ : syracuseStep 1540859 = 2311289) B2311289
theorem B3466025 : Blo 1539967 3466025 := bstep (se 2 (by rfl) ⟨1299759, by rfl⟩ : syracuseStep 3466025 = 2599519) B2599519
theorem B9872255 : Blo 1539967 9872255 := bstep (se 1 (by rfl) ⟨7404191, by rfl⟩ : syracuseStep 9872255 = 14808383) B14808383
theorem B1540991 : Blo 1539967 1540991 := bstep (se 1 (by rfl) ⟨1155743, by rfl⟩ : syracuseStep 1540991 = 2311487) B2311487
theorem B2311151 : Blo 1539967 2311151 := bstep (se 1 (by rfl) ⟨1733363, by rfl⟩ : syracuseStep 2311151 = 3466727) B3466727
theorem B2925659 : Blo 1539967 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B2311271 : Blo 1539967 2311271 := bstep (se 1 (by rfl) ⟨1733453, by rfl⟩ : syracuseStep 2311271 = 3466907) B3466907
theorem B1541439 : Blo 1539967 1541439 := bstep (se 1 (by rfl) ⟨1156079, by rfl⟩ : syracuseStep 1541439 = 2312159) B2312159
theorem B86689367 : Blo 1539967 86689367 := bstep (se 1 (by rfl) ⟨65017025, by rfl⟩ : syracuseStep 86689367 = 130034051) B130034051
theorem B5850863 : Blo 1539967 5850863 := bstep (se 1 (by rfl) ⟨4388147, by rfl⟩ : syracuseStep 5850863 = 8776295) B8776295
theorem B2311919 : Blo 1539967 2311919 := bstep (se 1 (by rfl) ⟨1733939, by rfl⟩ : syracuseStep 2311919 = 3467879) B3467879
theorem B5269319 : Blo 1539967 5269319 := bstep (se 1 (by rfl) ⟨3951989, by rfl⟩ : syracuseStep 5269319 = 7903979) B7903979
theorem B2312171 : Blo 1539967 2312171 := bstep (se 1 (by rfl) ⟨1734128, by rfl⟩ : syracuseStep 2312171 = 3468257) B3468257
theorem B3467519 : Blo 1539967 3467519 := bstep (se 1 (by rfl) ⟨2600639, by rfl⟩ : syracuseStep 3467519 = 5201279) B5201279
theorem B3467753 : Blo 1539967 3467753 := bstep (se 2 (by rfl) ⟨1300407, by rfl⟩ : syracuseStep 3467753 = 2600815) B2600815
theorem B2599465 : Blo 1539967 2599465 := bstep (se 2 (by rfl) ⟨974799, by rfl⟩ : syracuseStep 2599465 = 1949599) B1949599
theorem B7801433 : Blo 1539967 7801433 := bstep (se 2 (by rfl) ⟨2925537, by rfl⟩ : syracuseStep 7801433 = 5851075) B5851075
theorem B25668679 : Blo 1539967 25668679 := bstep (se 1 (by rfl) ⟨19251509, by rfl⟩ : syracuseStep 25668679 = 38503019) B38503019
theorem B54070483 : Blo 1539967 54070483 := bstep (se 1 (by rfl) ⟨40552862, by rfl⟩ : syracuseStep 54070483 = 81105725) B81105725
theorem B2600363 : Blo 1539967 2600363 := bstep (se 1 (by rfl) ⟨1950272, by rfl⟩ : syracuseStep 2600363 = 3900545) B3900545
theorem B24981371 : Blo 1539967 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B2600903 : Blo 1539967 2600903 := bstep (se 1 (by rfl) ⟨1950677, by rfl⟩ : syracuseStep 2600903 = 3901355) B3901355
theorem B5197931 : Blo 1539967 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B3006571 : Blo 1539967 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B3289385 : Blo 1539967 3289385 := bstep (se 2 (by rfl) ⟨1233519, by rfl⟩ : syracuseStep 3289385 = 2467039) B2467039
theorem B26685895 : Blo 1539967 26685895 := bstep (se 1 (by rfl) ⟨20014421, by rfl⟩ : syracuseStep 26685895 = 40028843) B40028843
theorem B14807767 : Blo 1539967 14807767 := bstep (se 1 (by rfl) ⟨11105825, by rfl⟩ : syracuseStep 14807767 = 22211651) B22211651
theorem B12669779 : Blo 1539967 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B44020615 : Blo 1539967 44020615 := bstep (se 1 (by rfl) ⟨33015461, by rfl⟩ : syracuseStep 44020615 = 66030923) B66030923
theorem B6583265 : Blo 1539967 6583265 := bstep (se 2 (by rfl) ⟨2468724, by rfl⟩ : syracuseStep 6583265 = 4937449) B4937449
theorem B14808041 : Blo 1539967 14808041 := bstep (se 2 (by rfl) ⟨5553015, by rfl⟩ : syracuseStep 14808041 = 11106031) B11106031
theorem B7796087 : Blo 1539967 7796087 := bstep (se 1 (by rfl) ⟨5847065, by rfl⟩ : syracuseStep 7796087 = 11694131) B11694131
theorem B15816073 : Blo 1539967 15816073 := bstep (se 2 (by rfl) ⟨5931027, by rfl⟩ : syracuseStep 15816073 = 11862055) B11862055
theorem B5199335 : Blo 1539967 5199335 := bstep (se 1 (by rfl) ⟨3899501, by rfl⟩ : syracuseStep 5199335 = 7799003) B7799003
theorem B2635247 : Blo 1539967 2635247 := bstep (se 1 (by rfl) ⟨1976435, by rfl⟩ : syracuseStep 2635247 = 3952871) B3952871
theorem B1644607 : Blo 1539967 1644607 := bstep (se 1 (by rfl) ⟨1233455, by rfl⟩ : syracuseStep 1644607 = 2466911) B2466911
theorem B35593015 : Blo 1539967 35593015 := bstep (se 1 (by rfl) ⟨26694761, by rfl⟩ : syracuseStep 35593015 = 53389523) B53389523
theorem B5847977 : Blo 1539967 5847977 := bstep (se 2 (by rfl) ⟨2192991, by rfl⟩ : syracuseStep 5847977 = 4385983) B4385983
theorem B5848159 : Blo 1539967 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B3898631 : Blo 1539967 3898631 := bstep (se 1 (by rfl) ⟨2923973, by rfl⟩ : syracuseStep 3898631 = 5847947) B5847947
theorem B5201225 : Blo 1539967 5201225 := bstep (se 2 (by rfl) ⟨1950459, by rfl⟩ : syracuseStep 5201225 = 3900919) B3900919
theorem B2923867 : Blo 1539967 2923867 := bstep (se 1 (by rfl) ⟨2192900, by rfl⟩ : syracuseStep 2923867 = 4385801) B4385801
theorem B1850779 : Blo 1539967 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B5201387 : Blo 1539967 5201387 := bstep (se 1 (by rfl) ⟨3901040, by rfl⟩ : syracuseStep 5201387 = 7802081) B7802081
theorem B27041363 : Blo 1539967 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B2776687 : Blo 1539967 2776687 := bstep (se 1 (by rfl) ⟨2082515, by rfl⟩ : syracuseStep 2776687 = 4165031) B4165031
theorem B9494441 : Blo 1539967 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B1540031 : Blo 1539967 1540031 := bstep (se 1 (by rfl) ⟨1155023, by rfl⟩ : syracuseStep 1540031 = 2310047) B2310047
theorem B1540091 : Blo 1539967 1540091 := bstep (se 1 (by rfl) ⟨1155068, by rfl⟩ : syracuseStep 1540091 = 2310137) B2310137
theorem B1540123 : Blo 1539967 1540123 := bstep (se 1 (by rfl) ⟨1155092, by rfl⟩ : syracuseStep 1540123 = 2310185) B2310185
theorem B3465287 : Blo 1539967 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B1540167 : Blo 1539967 1540167 := bstep (se 1 (by rfl) ⟨1155125, by rfl⟩ : syracuseStep 1540167 = 2310251) B2310251
theorem B3899785 : Blo 1539967 3899785 := bstep (se 2 (by rfl) ⟨1462419, by rfl⟩ : syracuseStep 3899785 = 2924839) B2924839
theorem B1540591 : Blo 1539967 1540591 := bstep (se 1 (by rfl) ⟨1155443, by rfl⟩ : syracuseStep 1540591 = 2310887) B2310887
theorem B3899897 : Blo 1539967 3899897 := bstep (se 2 (by rfl) ⟨1462461, by rfl⟩ : syracuseStep 3899897 = 2924923) B2924923
theorem B2310683 : Blo 1539967 2310683 := bstep (se 1 (by rfl) ⟨1733012, by rfl⟩ : syracuseStep 2310683 = 3466025) B3466025
theorem B8446519 : Blo 1539967 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B9872027 : Blo 1539967 9872027 := bstep (se 1 (by rfl) ⟨7404020, by rfl⟩ : syracuseStep 9872027 = 14808041) B14808041
theorem B1540767 : Blo 1539967 1540767 := bstep (se 1 (by rfl) ⟨1155575, by rfl⟩ : syracuseStep 1540767 = 2311151) B2311151
theorem B3465953 : Blo 1539967 3465953 := bstep (se 2 (by rfl) ⟨1299732, by rfl⟩ : syracuseStep 3465953 = 2599465) B2599465
theorem B1540847 : Blo 1539967 1540847 := bstep (se 1 (by rfl) ⟨1155635, by rfl⟩ : syracuseStep 1540847 = 2311271) B2311271
theorem B19743689 : Blo 1539967 19743689 := bstep (se 2 (by rfl) ⟨7403883, by rfl⟩ : syracuseStep 19743689 = 14807767) B14807767
theorem B3466223 : Blo 1539967 3466223 := bstep (se 1 (by rfl) ⟨2599667, by rfl⟩ : syracuseStep 3466223 = 5199335) B5199335
theorem B47457353 : Blo 1539967 47457353 := bstep (se 2 (by rfl) ⟨17796507, by rfl⟩ : syracuseStep 47457353 = 35593015) B35593015
theorem B3900575 : Blo 1539967 3900575 := bstep (se 1 (by rfl) ⟨2925431, by rfl⟩ : syracuseStep 3900575 = 5850863) B5850863
theorem B1541279 : Blo 1539967 1541279 := bstep (se 1 (by rfl) ⟨1155959, by rfl⟩ : syracuseStep 1541279 = 2311919) B2311919
theorem B1541447 : Blo 1539967 1541447 := bstep (se 1 (by rfl) ⟨1156085, by rfl⟩ : syracuseStep 1541447 = 2312171) B2312171
theorem B2311679 : Blo 1539967 2311679 := bstep (se 1 (by rfl) ⟨1733759, by rfl⟩ : syracuseStep 2311679 = 3467519) B3467519
theorem B2311835 : Blo 1539967 2311835 := bstep (se 1 (by rfl) ⟨1733876, by rfl⟩ : syracuseStep 2311835 = 3467753) B3467753
theorem B21088097 : Blo 1539967 21088097 := bstep (se 2 (by rfl) ⟨7908036, by rfl⟩ : syracuseStep 21088097 = 15816073) B15816073
theorem B2599087 : Blo 1539967 2599087 := bstep (se 1 (by rfl) ⟨1949315, by rfl⟩ : syracuseStep 2599087 = 3898631) B3898631
theorem B3467483 : Blo 1539967 3467483 := bstep (se 1 (by rfl) ⟨2600612, by rfl⟩ : syracuseStep 3467483 = 5201225) B5201225
theorem B3467591 : Blo 1539967 3467591 := bstep (se 1 (by rfl) ⟨2600693, by rfl⟩ : syracuseStep 3467591 = 5201387) B5201387
theorem B4008761 : Blo 1539967 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B7801757 : Blo 1539967 7801757 := bstep (se 3 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 7801757 = 2925659) B2925659
theorem B6581503 : Blo 1539967 6581503 := bstep (se 1 (by rfl) ⟨4936127, by rfl⟩ : syracuseStep 6581503 = 9872255) B9872255
theorem B35581193 : Blo 1539967 35581193 := bstep (se 2 (by rfl) ⟨13342947, by rfl⟩ : syracuseStep 35581193 = 26685895) B26685895
theorem B5197391 : Blo 1539967 5197391 := bstep (se 1 (by rfl) ⟨3898043, by rfl⟩ : syracuseStep 5197391 = 7796087) B7796087
theorem B1756831 : Blo 1539967 1756831 := bstep (se 1 (by rfl) ⟨1317623, by rfl⟩ : syracuseStep 1756831 = 2635247) B2635247
theorem B72093977 : Blo 1539967 72093977 := bstep (se 2 (by rfl) ⟨27035241, by rfl⟩ : syracuseStep 72093977 = 54070483) B54070483
theorem B1733575 : Blo 1539967 1733575 := bstep (se 1 (by rfl) ⟨1300181, by rfl⟩ : syracuseStep 1733575 = 2600363) B2600363
theorem B18027575 : Blo 1539967 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B6329627 : Blo 1539967 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B1733935 : Blo 1539967 1733935 := bstep (se 1 (by rfl) ⟨1300451, by rfl⟩ : syracuseStep 1733935 = 2600903) B2600903
theorem B2192923 : Blo 1539967 2192923 := bstep (se 1 (by rfl) ⟨1644692, by rfl⟩ : syracuseStep 2192923 = 3289385) B3289385
theorem B9016967 : Blo 1539967 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B8771237 : Blo 1539967 8771237 := bstep (se 4 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 8771237 = 1644607) B1644607
theorem B14808997 : Blo 1539967 14808997 := bstep (se 4 (by rfl) ⟨1388343, by rfl⟩ : syracuseStep 14808997 = 2776687) B2776687
theorem B4388843 : Blo 1539967 4388843 := bstep (se 1 (by rfl) ⟨3291632, by rfl⟩ : syracuseStep 4388843 = 6583265) B6583265
theorem B57792911 : Blo 1539967 57792911 := bstep (se 1 (by rfl) ⟨43344683, by rfl⟩ : syracuseStep 57792911 = 86689367) B86689367
theorem B58694153 : Blo 1539967 58694153 := bstep (se 2 (by rfl) ⟨22010307, by rfl⟩ : syracuseStep 58694153 = 44020615) B44020615
theorem B3512879 : Blo 1539967 3512879 := bstep (se 1 (by rfl) ⟨2634659, by rfl⟩ : syracuseStep 3512879 = 5269319) B5269319
theorem B34224905 : Blo 1539967 34224905 := bstep (se 2 (by rfl) ⟨12834339, by rfl⟩ : syracuseStep 34224905 = 25668679) B25668679
theorem B7797545 : Blo 1539967 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B5200955 : Blo 1539967 5200955 := bstep (se 1 (by rfl) ⟨3900716, by rfl⟩ : syracuseStep 5200955 = 7801433) B7801433
theorem B3898489 : Blo 1539967 3898489 := bstep (se 2 (by rfl) ⟨1461933, by rfl⟩ : syracuseStep 3898489 = 2923867) B2923867
theorem B3898651 : Blo 1539967 3898651 := bstep (se 1 (by rfl) ⟨2923988, by rfl⟩ : syracuseStep 3898651 = 5847977) B5847977
theorem B9870821 : Blo 1539967 9870821 := bstep (se 4 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 9870821 = 1850779) B1850779
theorem B16654247 : Blo 1539967 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B2310191 : Blo 1539967 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B48062651 : Blo 1539967 48062651 := bstep (se 1 (by rfl) ⟨36046988, by rfl⟩ : syracuseStep 48062651 = 72093977) B72093977
theorem B3465449 : Blo 1539967 3465449 := bstep (se 2 (by rfl) ⟨1299543, by rfl⟩ : syracuseStep 3465449 = 2599087) B2599087
theorem B1540455 : Blo 1539967 1540455 := bstep (se 1 (by rfl) ⟨1155341, by rfl⟩ : syracuseStep 1540455 = 2310683) B2310683
theorem B2310635 : Blo 1539967 2310635 := bstep (se 1 (by rfl) ⟨1732976, by rfl⟩ : syracuseStep 2310635 = 3465953) B3465953
theorem B2310815 : Blo 1539967 2310815 := bstep (se 1 (by rfl) ⟨1733111, by rfl⟩ : syracuseStep 2310815 = 3466223) B3466223
theorem B12018383 : Blo 1539967 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B31638235 : Blo 1539967 31638235 := bstep (se 1 (by rfl) ⟨23728676, by rfl⟩ : syracuseStep 31638235 = 47457353) B47457353
theorem B4219751 : Blo 1539967 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B1541119 : Blo 1539967 1541119 := bstep (se 1 (by rfl) ⟨1155839, by rfl⟩ : syracuseStep 1541119 = 2311679) B2311679
theorem B1541223 : Blo 1539967 1541223 := bstep (se 1 (by rfl) ⟨1155917, by rfl⟩ : syracuseStep 1541223 = 2311835) B2311835
theorem B14058731 : Blo 1539967 14058731 := bstep (se 1 (by rfl) ⟨10544048, by rfl⟩ : syracuseStep 14058731 = 21088097) B21088097
theorem B2311433 : Blo 1539967 2311433 := bstep (se 2 (by rfl) ⟨866787, by rfl⟩ : syracuseStep 2311433 = 1733575) B1733575
theorem B2925895 : Blo 1539967 2925895 := bstep (se 1 (by rfl) ⟨2194421, by rfl⟩ : syracuseStep 2925895 = 4388843) B4388843
theorem B156517741 : Blo 1539967 156517741 := bstep (se 3 (by rfl) ⟨29347076, by rfl⟩ : syracuseStep 156517741 = 58694153) B58694153
theorem B2311655 : Blo 1539967 2311655 := bstep (se 1 (by rfl) ⟨1733741, by rfl⟩ : syracuseStep 2311655 = 3467483) B3467483
theorem B2311727 : Blo 1539967 2311727 := bstep (se 1 (by rfl) ⟨1733795, by rfl⟩ : syracuseStep 2311727 = 3467591) B3467591
theorem B8775337 : Blo 1539967 8775337 := bstep (se 2 (by rfl) ⟨3290751, by rfl⟩ : syracuseStep 8775337 = 6581503) B6581503
theorem B24045245 : Blo 1539967 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B2311913 : Blo 1539967 2311913 := bstep (se 2 (by rfl) ⟨866967, by rfl⟩ : syracuseStep 2311913 = 1733935) B1733935
theorem B22816603 : Blo 1539967 22816603 := bstep (se 1 (by rfl) ⟨17112452, by rfl⟩ : syracuseStep 22816603 = 34224905) B34224905
theorem B2672507 : Blo 1539967 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B3467303 : Blo 1539967 3467303 := bstep (se 1 (by rfl) ⟨2600477, by rfl⟩ : syracuseStep 3467303 = 5200955) B5200955
theorem B6580547 : Blo 1539967 6580547 := bstep (se 1 (by rfl) ⟨4935410, by rfl⟩ : syracuseStep 6580547 = 9870821) B9870821
theorem B19745329 : Blo 1539967 19745329 := bstep (se 2 (by rfl) ⟨7404498, by rfl⟩ : syracuseStep 19745329 = 14808997) B14808997
theorem B11102831 : Blo 1539967 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B2599931 : Blo 1539967 2599931 := bstep (se 1 (by rfl) ⟨1949948, by rfl⟩ : syracuseStep 2599931 = 3899897) B3899897
theorem B6581351 : Blo 1539967 6581351 := bstep (se 1 (by rfl) ⟨4936013, by rfl⟩ : syracuseStep 6581351 = 9872027) B9872027
theorem B2600383 : Blo 1539967 2600383 := bstep (se 1 (by rfl) ⟨1950287, by rfl⟩ : syracuseStep 2600383 = 3900575) B3900575
theorem B5197985 : Blo 1539967 5197985 := bstep (se 2 (by rfl) ⟨1949244, by rfl⟩ : syracuseStep 5197985 = 3898489) B3898489
theorem B5198201 : Blo 1539967 5198201 := bstep (se 2 (by rfl) ⟨1949325, by rfl⟩ : syracuseStep 5198201 = 3898651) B3898651
theorem B5198363 : Blo 1539967 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B23720795 : Blo 1539967 23720795 := bstep (se 1 (by rfl) ⟨17790596, by rfl⟩ : syracuseStep 23720795 = 35581193) B35581193
theorem B11695589 : Blo 1539967 11695589 := bstep (se 4 (by rfl) ⟨1096461, by rfl⟩ : syracuseStep 11695589 = 2192923) B2192923
theorem B5199713 : Blo 1539967 5199713 := bstep (se 2 (by rfl) ⟨1949892, by rfl⟩ : syracuseStep 5199713 = 3899785) B3899785
theorem B13162459 : Blo 1539967 13162459 := bstep (se 1 (by rfl) ⟨9871844, by rfl⟩ : syracuseStep 13162459 = 19743689) B19743689
theorem B11262025 : Blo 1539967 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B154114429 : Blo 1539967 154114429 := bstep (se 3 (by rfl) ⟨28896455, by rfl⟩ : syracuseStep 154114429 = 57792911) B57792911
theorem B5847491 : Blo 1539967 5847491 := bstep (se 1 (by rfl) ⟨4385618, by rfl⟩ : syracuseStep 5847491 = 8771237) B8771237
theorem B2341919 : Blo 1539967 2341919 := bstep (se 1 (by rfl) ⟨1756439, by rfl⟩ : syracuseStep 2341919 = 3512879) B3512879
theorem B5201171 : Blo 1539967 5201171 := bstep (se 1 (by rfl) ⟨3900878, by rfl⟩ : syracuseStep 5201171 = 7801757) B7801757
theorem B2342441 : Blo 1539967 2342441 := bstep (se 2 (by rfl) ⟨878415, by rfl⟩ : syracuseStep 2342441 = 1756831) B1756831
theorem B3464927 : Blo 1539967 3464927 := bstep (se 1 (by rfl) ⟨2598695, by rfl⟩ : syracuseStep 3464927 = 5197391) B5197391
theorem B1540127 : Blo 1539967 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B15016033 : Blo 1539967 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B3465323 : Blo 1539967 3465323 := bstep (se 1 (by rfl) ⟨2598992, by rfl⟩ : syracuseStep 3465323 = 5197985) B5197985
theorem B2310299 : Blo 1539967 2310299 := bstep (se 1 (by rfl) ⟨1732724, by rfl⟩ : syracuseStep 2310299 = 3465449) B3465449
theorem B3465467 : Blo 1539967 3465467 := bstep (se 1 (by rfl) ⟨2599100, by rfl⟩ : syracuseStep 3465467 = 5198201) B5198201
theorem B1540423 : Blo 1539967 1540423 := bstep (se 1 (by rfl) ⟨1155317, by rfl⟩ : syracuseStep 1540423 = 2310635) B2310635
theorem B3465575 : Blo 1539967 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B1540543 : Blo 1539967 1540543 := bstep (se 1 (by rfl) ⟨1155407, by rfl⟩ : syracuseStep 1540543 = 2310815) B2310815
theorem B8012255 : Blo 1539967 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B1540955 : Blo 1539967 1540955 := bstep (se 1 (by rfl) ⟨1155716, by rfl⟩ : syracuseStep 1540955 = 2311433) B2311433
theorem B1541103 : Blo 1539967 1541103 := bstep (se 1 (by rfl) ⟨1155827, by rfl⟩ : syracuseStep 1541103 = 2311655) B2311655
theorem B1541151 : Blo 1539967 1541151 := bstep (se 1 (by rfl) ⟨1155863, by rfl⟩ : syracuseStep 1541151 = 2311727) B2311727
theorem B1541275 : Blo 1539967 1541275 := bstep (se 1 (by rfl) ⟨1155956, by rfl⟩ : syracuseStep 1541275 = 2311913) B2311913
theorem B3466475 : Blo 1539967 3466475 := bstep (se 1 (by rfl) ⟨2599856, by rfl⟩ : syracuseStep 3466475 = 5199713) B5199713
theorem B2311535 : Blo 1539967 2311535 := bstep (se 1 (by rfl) ⟨1733651, by rfl⟩ : syracuseStep 2311535 = 3467303) B3467303
theorem B3901193 : Blo 1539967 3901193 := bstep (se 2 (by rfl) ⟨1462947, by rfl⟩ : syracuseStep 3901193 = 2925895) B2925895
theorem B3467177 : Blo 1539967 3467177 := bstep (se 2 (by rfl) ⟨1300191, by rfl⟩ : syracuseStep 3467177 = 2600383) B2600383
theorem B3467447 : Blo 1539967 3467447 := bstep (se 1 (by rfl) ⟨2600585, by rfl⟩ : syracuseStep 3467447 = 5201171) B5201171
theorem B11700449 : Blo 1539967 11700449 := bstep (se 2 (by rfl) ⟨4387668, by rfl⟩ : syracuseStep 11700449 = 8775337) B8775337
theorem B17549945 : Blo 1539967 17549945 := bstep (se 2 (by rfl) ⟨6581229, by rfl⟩ : syracuseStep 17549945 = 13162459) B13162459
theorem B128167069 : Blo 1539967 128167069 := bstep (se 3 (by rfl) ⟨24031325, by rfl⟩ : syracuseStep 128167069 = 48062651) B48062651
theorem B15813863 : Blo 1539967 15813863 := bstep (se 1 (by rfl) ⟨11860397, by rfl⟩ : syracuseStep 15813863 = 23720795) B23720795
theorem B37489949 : Blo 1539967 37489949 := bstep (se 3 (by rfl) ⟨7029365, by rfl⟩ : syracuseStep 37489949 = 14058731) B14058731
theorem B42184313 : Blo 1539967 42184313 := bstep (se 2 (by rfl) ⟨15819117, by rfl⟩ : syracuseStep 42184313 = 31638235) B31638235
theorem B1781671 : Blo 1539967 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B4387031 : Blo 1539967 4387031 := bstep (se 1 (by rfl) ⟨3290273, by rfl⟩ : syracuseStep 4387031 = 6580547) B6580547
theorem B7401887 : Blo 1539967 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B1733287 : Blo 1539967 1733287 := bstep (se 1 (by rfl) ⟨1299965, by rfl⟩ : syracuseStep 1733287 = 2599931) B2599931
theorem B1561279 : Blo 1539967 1561279 := bstep (se 1 (by rfl) ⟨1170959, by rfl⟩ : syracuseStep 1561279 = 2341919) B2341919
theorem B4387567 : Blo 1539967 4387567 := bstep (se 1 (by rfl) ⟨3290675, by rfl⟩ : syracuseStep 4387567 = 6581351) B6581351
theorem B11252669 : Blo 1539967 11252669 := bstep (se 3 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 11252669 = 4219751) B4219751
theorem B1561627 : Blo 1539967 1561627 := bstep (se 1 (by rfl) ⟨1171220, by rfl⟩ : syracuseStep 1561627 = 2342441) B2342441
theorem B30422137 : Blo 1539967 30422137 := bstep (se 2 (by rfl) ⟨11408301, by rfl⟩ : syracuseStep 30422137 = 22816603) B22816603
theorem B205485905 : Blo 1539967 205485905 := bstep (se 2 (by rfl) ⟨77057214, by rfl⟩ : syracuseStep 205485905 = 154114429) B154114429
theorem B26327105 : Blo 1539967 26327105 := bstep (se 2 (by rfl) ⟨9872664, by rfl⟩ : syracuseStep 26327105 = 19745329) B19745329
theorem B7797059 : Blo 1539967 7797059 := bstep (se 1 (by rfl) ⟨5847794, by rfl⟩ : syracuseStep 7797059 = 11695589) B11695589
theorem B16030163 : Blo 1539967 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B3898327 : Blo 1539967 3898327 := bstep (se 1 (by rfl) ⟨2923745, by rfl⟩ : syracuseStep 3898327 = 5847491) B5847491
theorem B208690321 : Blo 1539967 208690321 := bstep (se 2 (by rfl) ⟨78258870, by rfl⟩ : syracuseStep 208690321 = 156517741) B156517741
theorem B2309951 : Blo 1539967 2309951 := bstep (se 1 (by rfl) ⟨1732463, by rfl⟩ : syracuseStep 2309951 = 3464927) B3464927
theorem B2310215 : Blo 1539967 2310215 := bstep (se 1 (by rfl) ⟨1732661, by rfl⟩ : syracuseStep 2310215 = 3465323) B3465323
theorem B1540199 : Blo 1539967 1540199 := bstep (se 1 (by rfl) ⟨1155149, by rfl⟩ : syracuseStep 1540199 = 2310299) B2310299
theorem B20021377 : Blo 1539967 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B2924687 : Blo 1539967 2924687 := bstep (se 1 (by rfl) ⟨2193515, by rfl⟩ : syracuseStep 2924687 = 4387031) B4387031
theorem B2310311 : Blo 1539967 2310311 := bstep (se 1 (by rfl) ⟨1732733, by rfl⟩ : syracuseStep 2310311 = 3465467) B3465467
theorem B2310383 : Blo 1539967 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B2310983 : Blo 1539967 2310983 := bstep (se 1 (by rfl) ⟨1733237, by rfl⟩ : syracuseStep 2310983 = 3466475) B3466475
theorem B2311049 : Blo 1539967 2311049 := bstep (se 2 (by rfl) ⟨866643, by rfl⟩ : syracuseStep 2311049 = 1733287) B1733287
theorem B1541023 : Blo 1539967 1541023 := bstep (se 1 (by rfl) ⟨1155767, by rfl⟩ : syracuseStep 1541023 = 2311535) B2311535
theorem B2081705 : Blo 1539967 2081705 := bstep (se 2 (by rfl) ⟨780639, by rfl⟩ : syracuseStep 2081705 = 1561279) B1561279
theorem B5850089 : Blo 1539967 5850089 := bstep (se 2 (by rfl) ⟨2193783, by rfl⟩ : syracuseStep 5850089 = 4387567) B4387567
theorem B42747101 : Blo 1539967 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B21366013 : Blo 1539967 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B2311451 : Blo 1539967 2311451 := bstep (se 1 (by rfl) ⟨1733588, by rfl⟩ : syracuseStep 2311451 = 3467177) B3467177
theorem B2311631 : Blo 1539967 2311631 := bstep (se 1 (by rfl) ⟨1733723, by rfl⟩ : syracuseStep 2311631 = 3467447) B3467447
theorem B7800299 : Blo 1539967 7800299 := bstep (se 1 (by rfl) ⟨5850224, by rfl⟩ : syracuseStep 7800299 = 11700449) B11700449
theorem B11699963 : Blo 1539967 11699963 := bstep (se 1 (by rfl) ⟨8774972, by rfl⟩ : syracuseStep 11699963 = 17549945) B17549945
theorem B4934591 : Blo 1539967 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B4452060181 : Blo 1539967 4452060181 := bstep (se 6 (by rfl) ⟨104345160, by rfl⟩ : syracuseStep 4452060181 = 208690321) B208690321
theorem B2600795 : Blo 1539967 2600795 := bstep (se 1 (by rfl) ⟨1950596, by rfl⟩ : syracuseStep 2600795 = 3901193) B3901193
theorem B136990603 : Blo 1539967 136990603 := bstep (se 1 (by rfl) ⟨102742952, by rfl⟩ : syracuseStep 136990603 = 205485905) B205485905
theorem B5197769 : Blo 1539967 5197769 := bstep (se 2 (by rfl) ⟨1949163, by rfl⟩ : syracuseStep 5197769 = 3898327) B3898327
theorem B17551403 : Blo 1539967 17551403 := bstep (se 1 (by rfl) ⟨13163552, by rfl⟩ : syracuseStep 17551403 = 26327105) B26327105
theorem B40562849 : Blo 1539967 40562849 := bstep (se 2 (by rfl) ⟨15211068, by rfl⟩ : syracuseStep 40562849 = 30422137) B30422137
theorem B170889425 : Blo 1539967 170889425 := bstep (se 2 (by rfl) ⟨64083534, by rfl⟩ : syracuseStep 170889425 = 128167069) B128167069
theorem B5198039 : Blo 1539967 5198039 := bstep (se 1 (by rfl) ⟨3898529, by rfl⟩ : syracuseStep 5198039 = 7797059) B7797059
theorem B8328677 : Blo 1539967 8328677 := bstep (se 4 (by rfl) ⟨780813, by rfl⟩ : syracuseStep 8328677 = 1561627) B1561627
theorem B10542575 : Blo 1539967 10542575 := bstep (se 1 (by rfl) ⟨7906931, by rfl⟩ : syracuseStep 10542575 = 15813863) B15813863
theorem B24993299 : Blo 1539967 24993299 := bstep (se 1 (by rfl) ⟨18744974, by rfl⟩ : syracuseStep 24993299 = 37489949) B37489949
theorem B28122875 : Blo 1539967 28122875 := bstep (se 1 (by rfl) ⟨21092156, by rfl⟩ : syracuseStep 28122875 = 42184313) B42184313
theorem B30007117 : Blo 1539967 30007117 := bstep (se 3 (by rfl) ⟨5626334, by rfl⟩ : syracuseStep 30007117 = 11252669) B11252669
theorem B1539967 : Blo 1539967 1539967 := bstep (se 1 (by rfl) ⟨1154975, by rfl⟩ : syracuseStep 1539967 = 2309951) B2309951
theorem B2375561 : Blo 1539967 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B1540143 : Blo 1539967 1540143 := bstep (se 1 (by rfl) ⟨1155107, by rfl⟩ : syracuseStep 1540143 = 2310215) B2310215
theorem B27041899 : Blo 1539967 27041899 := bstep (se 1 (by rfl) ⟨20281424, by rfl⟩ : syracuseStep 27041899 = 40562849) B40562849
theorem B1540207 : Blo 1539967 1540207 := bstep (se 1 (by rfl) ⟨1155155, by rfl⟩ : syracuseStep 1540207 = 2310311) B2310311
theorem B113926283 : Blo 1539967 113926283 := bstep (se 1 (by rfl) ⟨85444712, by rfl⟩ : syracuseStep 113926283 = 170889425) B170889425
theorem B3465359 : Blo 1539967 3465359 := bstep (se 1 (by rfl) ⟨2599019, by rfl⟩ : syracuseStep 3465359 = 5198039) B5198039
theorem B1540255 : Blo 1539967 1540255 := bstep (se 1 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 1540255 = 2310383) B2310383
theorem B7799165 : Blo 1539967 7799165 := bstep (se 3 (by rfl) ⟨1462343, by rfl⟩ : syracuseStep 7799165 = 2924687) B2924687
theorem B1540655 : Blo 1539967 1540655 := bstep (se 1 (by rfl) ⟨1155491, by rfl⟩ : syracuseStep 1540655 = 2310983) B2310983
theorem B1540699 : Blo 1539967 1540699 := bstep (se 1 (by rfl) ⟨1155524, by rfl⟩ : syracuseStep 1540699 = 2311049) B2311049
theorem B3900059 : Blo 1539967 3900059 := bstep (se 1 (by rfl) ⟨2925044, by rfl⟩ : syracuseStep 3900059 = 5850089) B5850089
theorem B1540967 : Blo 1539967 1540967 := bstep (se 1 (by rfl) ⟨1155725, by rfl⟩ : syracuseStep 1540967 = 2311451) B2311451
theorem B1541087 : Blo 1539967 1541087 := bstep (se 1 (by rfl) ⟨1155815, by rfl⟩ : syracuseStep 1541087 = 2311631) B2311631
theorem B7799975 : Blo 1539967 7799975 := bstep (se 1 (by rfl) ⟨5849981, by rfl⟩ : syracuseStep 7799975 = 11699963) B11699963
theorem B22209805 : Blo 1539967 22209805 := bstep (se 3 (by rfl) ⟨4164338, by rfl⟩ : syracuseStep 22209805 = 8328677) B8328677
theorem B5936080241 : Blo 1539967 5936080241 := bstep (se 2 (by rfl) ⟨2226030090, by rfl⟩ : syracuseStep 5936080241 = 4452060181) B4452060181
theorem B1583707 : Blo 1539967 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B11700935 : Blo 1539967 11700935 := bstep (se 1 (by rfl) ⟨8775701, by rfl⟩ : syracuseStep 11700935 = 17551403) B17551403
theorem B28488017 : Blo 1539967 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B22204853 : Blo 1539967 22204853 := bstep (se 5 (by rfl) ⟨1040852, by rfl⟩ : syracuseStep 22204853 = 2081705) B2081705
theorem B3289727 : Blo 1539967 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B18748583 : Blo 1539967 18748583 := bstep (se 1 (by rfl) ⟨14061437, by rfl⟩ : syracuseStep 18748583 = 28122875) B28122875
theorem B182654137 : Blo 1539967 182654137 := bstep (se 2 (by rfl) ⟨68495301, by rfl⟩ : syracuseStep 182654137 = 136990603) B136990603
theorem B1733863 : Blo 1539967 1733863 := bstep (se 1 (by rfl) ⟨1300397, by rfl⟩ : syracuseStep 1733863 = 2600795) B2600795
theorem B26695169 : Blo 1539967 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B28498067 : Blo 1539967 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B5200199 : Blo 1539967 5200199 := bstep (se 1 (by rfl) ⟨3900149, by rfl⟩ : syracuseStep 5200199 = 7800299) B7800299
theorem B160037957 : Blo 1539967 160037957 := bstep (se 4 (by rfl) ⟨15003558, by rfl⟩ : syracuseStep 160037957 = 30007117) B30007117
theorem B7028383 : Blo 1539967 7028383 := bstep (se 1 (by rfl) ⟨5271287, by rfl⟩ : syracuseStep 7028383 = 10542575) B10542575
theorem B16662199 : Blo 1539967 16662199 := bstep (se 1 (by rfl) ⟨12496649, by rfl⟩ : syracuseStep 16662199 = 24993299) B24993299
theorem B3465179 : Blo 1539967 3465179 := bstep (se 1 (by rfl) ⟨2598884, by rfl⟩ : syracuseStep 3465179 = 5197769) B5197769
theorem B2310239 : Blo 1539967 2310239 := bstep (se 1 (by rfl) ⟨1732679, by rfl⟩ : syracuseStep 2310239 = 3465359) B3465359
theorem B14803235 : Blo 1539967 14803235 := bstep (se 1 (by rfl) ⟨11102426, by rfl⟩ : syracuseStep 14803235 = 22204853) B22204853
theorem B18998711 : Blo 1539967 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B3466799 : Blo 1539967 3466799 := bstep (se 1 (by rfl) ⟨2600099, by rfl⟩ : syracuseStep 3466799 = 5200199) B5200199
theorem B2311817 : Blo 1539967 2311817 := bstep (se 2 (by rfl) ⟨866931, by rfl⟩ : syracuseStep 2311817 = 1733863) B1733863
theorem B7800623 : Blo 1539967 7800623 := bstep (se 1 (by rfl) ⟨5850467, by rfl⟩ : syracuseStep 7800623 = 11700935) B11700935
theorem B75950855 : Blo 1539967 75950855 := bstep (se 1 (by rfl) ⟨56963141, by rfl⟩ : syracuseStep 75950855 = 113926283) B113926283
theorem B36055865 : Blo 1539967 36055865 := bstep (se 2 (by rfl) ⟨13520949, by rfl⟩ : syracuseStep 36055865 = 27041899) B27041899
theorem B18992011 : Blo 1539967 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B2600039 : Blo 1539967 2600039 := bstep (se 1 (by rfl) ⟨1950029, by rfl⟩ : syracuseStep 2600039 = 3900059) B3900059
theorem B3957386827 : Blo 1539967 3957386827 := bstep (se 1 (by rfl) ⟨2968040120, by rfl⟩ : syracuseStep 3957386827 = 5936080241) B5936080241
theorem B17796779 : Blo 1539967 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B426767885 : Blo 1539967 426767885 := bstep (se 3 (by rfl) ⟨80018978, by rfl⟩ : syracuseStep 426767885 = 160037957) B160037957
theorem B5199443 : Blo 1539967 5199443 := bstep (se 1 (by rfl) ⟨3899582, by rfl⟩ : syracuseStep 5199443 = 7799165) B7799165
theorem B2193151 : Blo 1539967 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B5199983 : Blo 1539967 5199983 := bstep (se 1 (by rfl) ⟨3899987, by rfl⟩ : syracuseStep 5199983 = 7799975) B7799975
theorem B12499055 : Blo 1539967 12499055 := bstep (se 1 (by rfl) ⟨9374291, by rfl⟩ : syracuseStep 12499055 = 18748583) B18748583
theorem B2111609 : Blo 1539967 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B243538849 : Blo 1539967 243538849 := bstep (se 2 (by rfl) ⟨91327068, by rfl⟩ : syracuseStep 243538849 = 182654137) B182654137
theorem B29613073 : Blo 1539967 29613073 := bstep (se 2 (by rfl) ⟨11104902, by rfl⟩ : syracuseStep 29613073 = 22209805) B22209805
theorem B9371177 : Blo 1539967 9371177 := bstep (se 2 (by rfl) ⟨3514191, by rfl⟩ : syracuseStep 9371177 = 7028383) B7028383
theorem B22216265 : Blo 1539967 22216265 := bstep (se 2 (by rfl) ⟨8331099, by rfl⟩ : syracuseStep 22216265 = 16662199) B16662199
theorem B2310119 : Blo 1539967 2310119 := bstep (se 1 (by rfl) ⟨1732589, by rfl⟩ : syracuseStep 2310119 = 3465179) B3465179
theorem B1540159 : Blo 1539967 1540159 := bstep (se 1 (by rfl) ⟨1155119, by rfl⟩ : syracuseStep 1540159 = 2310239) B2310239
theorem B12665807 : Blo 1539967 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B2311199 : Blo 1539967 2311199 := bstep (se 1 (by rfl) ⟨1733399, by rfl⟩ : syracuseStep 2311199 = 3466799) B3466799
theorem B3466295 : Blo 1539967 3466295 := bstep (se 1 (by rfl) ⟨2599721, by rfl⟩ : syracuseStep 3466295 = 5199443) B5199443
theorem B1541211 : Blo 1539967 1541211 := bstep (se 1 (by rfl) ⟨1155908, by rfl⟩ : syracuseStep 1541211 = 2311817) B2311817
theorem B25322681 : Blo 1539967 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B3466655 : Blo 1539967 3466655 := bstep (se 1 (by rfl) ⟨2599991, by rfl⟩ : syracuseStep 3466655 = 5199983) B5199983
theorem B8332703 : Blo 1539967 8332703 := bstep (se 1 (by rfl) ⟨6249527, by rfl⟩ : syracuseStep 8332703 = 12499055) B12499055
theorem B24037243 : Blo 1539967 24037243 := bstep (se 1 (by rfl) ⟨18027932, by rfl⟩ : syracuseStep 24037243 = 36055865) B36055865
theorem B11864519 : Blo 1539967 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B5630957 : Blo 1539967 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B284511923 : Blo 1539967 284511923 := bstep (se 1 (by rfl) ⟨213383942, by rfl⟩ : syracuseStep 284511923 = 426767885) B426767885
theorem B324718465 : Blo 1539967 324718465 := bstep (se 2 (by rfl) ⟨121769424, by rfl⟩ : syracuseStep 324718465 = 243538849) B243538849
theorem B1733359 : Blo 1539967 1733359 := bstep (se 1 (by rfl) ⟨1300019, by rfl⟩ : syracuseStep 1733359 = 2600039) B2600039
theorem B6247451 : Blo 1539967 6247451 := bstep (se 1 (by rfl) ⟨4685588, by rfl⟩ : syracuseStep 6247451 = 9371177) B9371177
theorem B9868823 : Blo 1539967 9868823 := bstep (se 1 (by rfl) ⟨7401617, by rfl⟩ : syracuseStep 9868823 = 14803235) B14803235
theorem B5200415 : Blo 1539967 5200415 := bstep (se 1 (by rfl) ⟨3900311, by rfl⟩ : syracuseStep 5200415 = 7800623) B7800623
theorem B39484097 : Blo 1539967 39484097 := bstep (se 2 (by rfl) ⟨14806536, by rfl⟩ : syracuseStep 39484097 = 29613073) B29613073
theorem B50633903 : Blo 1539967 50633903 := bstep (se 1 (by rfl) ⟨37975427, by rfl⟩ : syracuseStep 50633903 = 75950855) B75950855
theorem B5276515769 : Blo 1539967 5276515769 := bstep (se 2 (by rfl) ⟨1978693413, by rfl⟩ : syracuseStep 5276515769 = 3957386827) B3957386827
theorem B2924201 : Blo 1539967 2924201 := bstep (se 2 (by rfl) ⟨1096575, by rfl⟩ : syracuseStep 2924201 = 2193151) B2193151
theorem B14810843 : Blo 1539967 14810843 := bstep (se 1 (by rfl) ⟨11108132, by rfl⟩ : syracuseStep 14810843 = 22216265) B22216265
theorem B1540079 : Blo 1539967 1540079 := bstep (se 1 (by rfl) ⟨1155059, by rfl⟩ : syracuseStep 1540079 = 2310119) B2310119
theorem B1540799 : Blo 1539967 1540799 := bstep (se 1 (by rfl) ⟨1155599, by rfl⟩ : syracuseStep 1540799 = 2311199) B2311199
theorem B2310863 : Blo 1539967 2310863 := bstep (se 1 (by rfl) ⟨1733147, by rfl⟩ : syracuseStep 2310863 = 3466295) B3466295
theorem B2311103 : Blo 1539967 2311103 := bstep (se 1 (by rfl) ⟨1733327, by rfl⟩ : syracuseStep 2311103 = 3466655) B3466655
theorem B5555135 : Blo 1539967 5555135 := bstep (se 1 (by rfl) ⟨4166351, by rfl⟩ : syracuseStep 5555135 = 8332703) B8332703
theorem B2311145 : Blo 1539967 2311145 := bstep (se 2 (by rfl) ⟨866679, by rfl⟩ : syracuseStep 2311145 = 1733359) B1733359
theorem B6579215 : Blo 1539967 6579215 := bstep (se 1 (by rfl) ⟨4934411, by rfl⟩ : syracuseStep 6579215 = 9868823) B9868823
theorem B3466943 : Blo 1539967 3466943 := bstep (se 1 (by rfl) ⟨2600207, by rfl⟩ : syracuseStep 3466943 = 5200415) B5200415
theorem B26322731 : Blo 1539967 26322731 := bstep (se 1 (by rfl) ⟨19742048, by rfl⟩ : syracuseStep 26322731 = 39484097) B39484097
theorem B128198629 : Blo 1539967 128198629 := bstep (se 4 (by rfl) ⟨12018621, by rfl⟩ : syracuseStep 128198629 = 24037243) B24037243
theorem B3753971 : Blo 1539967 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B9873895 : Blo 1539967 9873895 := bstep (se 1 (by rfl) ⟨7405421, by rfl⟩ : syracuseStep 9873895 = 14810843) B14810843
theorem B432957953 : Blo 1539967 432957953 := bstep (se 2 (by rfl) ⟨162359232, by rfl⟩ : syracuseStep 432957953 = 324718465) B324718465
theorem B4164967 : Blo 1539967 4164967 := bstep (se 1 (by rfl) ⟨3123725, by rfl⟩ : syracuseStep 4164967 = 6247451) B6247451
theorem B7909679 : Blo 1539967 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B33755935 : Blo 1539967 33755935 := bstep (se 1 (by rfl) ⟨25316951, by rfl⟩ : syracuseStep 33755935 = 50633903) B50633903
theorem B189674615 : Blo 1539967 189674615 := bstep (se 1 (by rfl) ⟨142255961, by rfl⟩ : syracuseStep 189674615 = 284511923) B284511923
theorem B8443871 : Blo 1539967 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B16881787 : Blo 1539967 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B7797869 : Blo 1539967 7797869 := bstep (se 3 (by rfl) ⟨1462100, by rfl⟩ : syracuseStep 7797869 = 2924201) B2924201
theorem B3517677179 : Blo 1539967 3517677179 := bstep (se 1 (by rfl) ⟨2638257884, by rfl⟩ : syracuseStep 3517677179 = 5276515769) B5276515769
theorem B1540575 : Blo 1539967 1540575 := bstep (se 1 (by rfl) ⟨1155431, by rfl⟩ : syracuseStep 1540575 = 2310863) B2310863
theorem B1540735 : Blo 1539967 1540735 := bstep (se 1 (by rfl) ⟨1155551, by rfl⟩ : syracuseStep 1540735 = 2311103) B2311103
theorem B3703423 : Blo 1539967 3703423 := bstep (se 1 (by rfl) ⟨2777567, by rfl⟩ : syracuseStep 3703423 = 5555135) B5555135
theorem B13165193 : Blo 1539967 13165193 := bstep (se 2 (by rfl) ⟨4936947, by rfl⟩ : syracuseStep 13165193 = 9873895) B9873895
theorem B1540763 : Blo 1539967 1540763 := bstep (se 1 (by rfl) ⟨1155572, by rfl⟩ : syracuseStep 1540763 = 2311145) B2311145
theorem B45007913 : Blo 1539967 45007913 := bstep (se 2 (by rfl) ⟨16877967, by rfl⟩ : syracuseStep 45007913 = 33755935) B33755935
theorem B2311295 : Blo 1539967 2311295 := bstep (se 1 (by rfl) ⟨1733471, by rfl⟩ : syracuseStep 2311295 = 3466943) B3466943
theorem B17548487 : Blo 1539967 17548487 := bstep (se 1 (by rfl) ⟨13161365, by rfl⟩ : syracuseStep 17548487 = 26322731) B26322731
theorem B5629247 : Blo 1539967 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B288638635 : Blo 1539967 288638635 := bstep (se 1 (by rfl) ⟨216478976, by rfl⟩ : syracuseStep 288638635 = 432957953) B432957953
theorem B2345118119 : Blo 1539967 2345118119 := bstep (se 1 (by rfl) ⟨1758838589, by rfl⟩ : syracuseStep 2345118119 = 3517677179) B3517677179
theorem B4386143 : Blo 1539967 4386143 := bstep (se 1 (by rfl) ⟨3289607, by rfl⟩ : syracuseStep 4386143 = 6579215) B6579215
theorem B2502647 : Blo 1539967 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B5198579 : Blo 1539967 5198579 := bstep (se 1 (by rfl) ⟨3898934, by rfl⟩ : syracuseStep 5198579 = 7797869) B7797869
theorem B170931505 : Blo 1539967 170931505 := bstep (se 2 (by rfl) ⟨64099314, by rfl⟩ : syracuseStep 170931505 = 128198629) B128198629
theorem B22509049 : Blo 1539967 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B5273119 : Blo 1539967 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B126449743 : Blo 1539967 126449743 := bstep (se 1 (by rfl) ⟨94837307, by rfl⟩ : syracuseStep 126449743 = 189674615) B189674615
theorem B5553289 : Blo 1539967 5553289 := bstep (se 2 (by rfl) ⟨2082483, by rfl⟩ : syracuseStep 5553289 = 4164967) B4164967
theorem B168599657 : Blo 1539967 168599657 := bstep (se 2 (by rfl) ⟨63224871, by rfl⟩ : syracuseStep 168599657 = 126449743) B126449743
theorem B28123301 : Blo 1539967 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B3465719 : Blo 1539967 3465719 := bstep (se 1 (by rfl) ⟨2599289, by rfl⟩ : syracuseStep 3465719 = 5198579) B5198579
theorem B1540863 : Blo 1539967 1540863 := bstep (se 1 (by rfl) ⟨1155647, by rfl⟩ : syracuseStep 1540863 = 2311295) B2311295
theorem B11698991 : Blo 1539967 11698991 := bstep (se 1 (by rfl) ⟨8774243, by rfl⟩ : syracuseStep 11698991 = 17548487) B17548487
theorem B3752831 : Blo 1539967 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B1563412079 : Blo 1539967 1563412079 := bstep (se 1 (by rfl) ⟨1172559059, by rfl⟩ : syracuseStep 1563412079 = 2345118119) B2345118119
theorem B8776795 : Blo 1539967 8776795 := bstep (se 1 (by rfl) ⟨6582596, by rfl⟩ : syracuseStep 8776795 = 13165193) B13165193
theorem B30012065 : Blo 1539967 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B1668431 : Blo 1539967 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B30005275 : Blo 1539967 30005275 := bstep (se 1 (by rfl) ⟨22503956, by rfl⟩ : syracuseStep 30005275 = 45007913) B45007913
theorem B4937897 : Blo 1539967 4937897 := bstep (se 2 (by rfl) ⟨1851711, by rfl⟩ : syracuseStep 4937897 = 3703423) B3703423
theorem B7404385 : Blo 1539967 7404385 := bstep (se 2 (by rfl) ⟨2776644, by rfl⟩ : syracuseStep 7404385 = 5553289) B5553289
theorem B227908673 : Blo 1539967 227908673 := bstep (se 2 (by rfl) ⟨85465752, by rfl⟩ : syracuseStep 227908673 = 170931505) B170931505
theorem B384851513 : Blo 1539967 384851513 := bstep (se 2 (by rfl) ⟨144319317, by rfl⟩ : syracuseStep 384851513 = 288638635) B288638635
theorem B2924095 : Blo 1539967 2924095 := bstep (se 1 (by rfl) ⟨2193071, by rfl⟩ : syracuseStep 2924095 = 4386143) B4386143
theorem B2310479 : Blo 1539967 2310479 := bstep (se 1 (by rfl) ⟨1732859, by rfl⟩ : syracuseStep 2310479 = 3465719) B3465719
theorem B7799327 : Blo 1539967 7799327 := bstep (se 1 (by rfl) ⟨5849495, by rfl⟩ : syracuseStep 7799327 = 11698991) B11698991
theorem B4449149 : Blo 1539967 4449149 := bstep (se 3 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 4449149 = 1668431) B1668431
theorem B9872513 : Blo 1539967 9872513 := bstep (se 2 (by rfl) ⟨3702192, by rfl⟩ : syracuseStep 9872513 = 7404385) B7404385
theorem B151939115 : Blo 1539967 151939115 := bstep (se 1 (by rfl) ⟨113954336, by rfl⟩ : syracuseStep 151939115 = 227908673) B227908673
theorem B256567675 : Blo 1539967 256567675 := bstep (se 1 (by rfl) ⟨192425756, by rfl⟩ : syracuseStep 256567675 = 384851513) B384851513
theorem B20008043 : Blo 1539967 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B11702393 : Blo 1539967 11702393 := bstep (se 2 (by rfl) ⟨4388397, by rfl⟩ : syracuseStep 11702393 = 8776795) B8776795
theorem B10007549 : Blo 1539967 10007549 := bstep (se 3 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 10007549 = 3752831) B3752831
theorem B40007033 : Blo 1539967 40007033 := bstep (se 2 (by rfl) ⟨15002637, by rfl⟩ : syracuseStep 40007033 = 30005275) B30005275
theorem B18748867 : Blo 1539967 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B449599085 : Blo 1539967 449599085 := bstep (se 3 (by rfl) ⟨84299828, by rfl⟩ : syracuseStep 449599085 = 168599657) B168599657
theorem B1042274719 : Blo 1539967 1042274719 := bstep (se 1 (by rfl) ⟨781706039, by rfl⟩ : syracuseStep 1042274719 = 1563412079) B1563412079
theorem B3291931 : Blo 1539967 3291931 := bstep (se 1 (by rfl) ⟨2468948, by rfl⟩ : syracuseStep 3291931 = 4937897) B4937897
theorem B3898793 : Blo 1539967 3898793 := bstep (se 2 (by rfl) ⟨1462047, by rfl⟩ : syracuseStep 3898793 = 2924095) B2924095
theorem B1540319 : Blo 1539967 1540319 := bstep (se 1 (by rfl) ⟨1155239, by rfl⟩ : syracuseStep 1540319 = 2310479) B2310479
theorem B342090233 : Blo 1539967 342090233 := bstep (se 2 (by rfl) ⟨128283837, by rfl⟩ : syracuseStep 342090233 = 256567675) B256567675
theorem B1389699625 : Blo 1539967 1389699625 := bstep (se 2 (by rfl) ⟨521137359, by rfl⟩ : syracuseStep 1389699625 = 1042274719) B1042274719
theorem B2966099 : Blo 1539967 2966099 := bstep (se 1 (by rfl) ⟨2224574, by rfl⟩ : syracuseStep 2966099 = 4449149) B4449149
theorem B13338695 : Blo 1539967 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B2599195 : Blo 1539967 2599195 := bstep (se 1 (by rfl) ⟨1949396, by rfl⟩ : syracuseStep 2599195 = 3898793) B3898793
theorem B7801595 : Blo 1539967 7801595 := bstep (se 1 (by rfl) ⟨5851196, by rfl⟩ : syracuseStep 7801595 = 11702393) B11702393
theorem B6671699 : Blo 1539967 6671699 := bstep (se 1 (by rfl) ⟨5003774, by rfl⟩ : syracuseStep 6671699 = 10007549) B10007549
theorem B6581675 : Blo 1539967 6581675 := bstep (se 1 (by rfl) ⟨4936256, by rfl⟩ : syracuseStep 6581675 = 9872513) B9872513
theorem B299732723 : Blo 1539967 299732723 := bstep (se 1 (by rfl) ⟨224799542, by rfl⟩ : syracuseStep 299732723 = 449599085) B449599085
theorem B24998489 : Blo 1539967 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B5199551 : Blo 1539967 5199551 := bstep (se 1 (by rfl) ⟨3899663, by rfl⟩ : syracuseStep 5199551 = 7799327) B7799327
theorem B26671355 : Blo 1539967 26671355 := bstep (se 1 (by rfl) ⟨20003516, by rfl⟩ : syracuseStep 26671355 = 40007033) B40007033
theorem B4389241 : Blo 1539967 4389241 := bstep (se 2 (by rfl) ⟨1645965, by rfl⟩ : syracuseStep 4389241 = 3291931) B3291931
theorem B101292743 : Blo 1539967 101292743 := bstep (se 1 (by rfl) ⟨75969557, by rfl⟩ : syracuseStep 101292743 = 151939115) B151939115
theorem B3465593 : Blo 1539967 3465593 := bstep (se 2 (by rfl) ⟨1299597, by rfl⟩ : syracuseStep 3465593 = 2599195) B2599195
theorem B1852932833 : Blo 1539967 1852932833 := bstep (se 2 (by rfl) ⟨694849812, by rfl⟩ : syracuseStep 1852932833 = 1389699625) B1389699625
theorem B3466367 : Blo 1539967 3466367 := bstep (se 1 (by rfl) ⟨2599775, by rfl⟩ : syracuseStep 3466367 = 5199551) B5199551
theorem B67528495 : Blo 1539967 67528495 := bstep (se 1 (by rfl) ⟨50646371, by rfl⟩ : syracuseStep 67528495 = 101292743) B101292743
theorem B199821815 : Blo 1539967 199821815 := bstep (se 1 (by rfl) ⟨149866361, by rfl⟩ : syracuseStep 199821815 = 299732723) B299732723
theorem B228060155 : Blo 1539967 228060155 := bstep (se 1 (by rfl) ⟨171045116, by rfl⟩ : syracuseStep 228060155 = 342090233) B342090233
theorem B16665659 : Blo 1539967 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B5852321 : Blo 1539967 5852321 := bstep (se 2 (by rfl) ⟨2194620, by rfl⟩ : syracuseStep 5852321 = 4389241) B4389241
theorem B8892463 : Blo 1539967 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B17780903 : Blo 1539967 17780903 := bstep (se 1 (by rfl) ⟨13335677, by rfl⟩ : syracuseStep 17780903 = 26671355) B26671355
theorem B7909597 : Blo 1539967 7909597 := bstep (se 3 (by rfl) ⟨1483049, by rfl⟩ : syracuseStep 7909597 = 2966099) B2966099
theorem B4387783 : Blo 1539967 4387783 := bstep (se 1 (by rfl) ⟨3290837, by rfl⟩ : syracuseStep 4387783 = 6581675) B6581675
theorem B5201063 : Blo 1539967 5201063 := bstep (se 1 (by rfl) ⟨3900797, by rfl⟩ : syracuseStep 5201063 = 7801595) B7801595
theorem B4447799 : Blo 1539967 4447799 := bstep (se 1 (by rfl) ⟨3335849, by rfl⟩ : syracuseStep 4447799 = 6671699) B6671699
theorem B11853935 : Blo 1539967 11853935 := bstep (se 1 (by rfl) ⟨8890451, by rfl⟩ : syracuseStep 11853935 = 17780903) B17780903
theorem B2310395 : Blo 1539967 2310395 := bstep (se 1 (by rfl) ⟨1732796, by rfl⟩ : syracuseStep 2310395 = 3465593) B3465593
theorem B1235288555 : Blo 1539967 1235288555 := bstep (se 1 (by rfl) ⟨926466416, by rfl⟩ : syracuseStep 1235288555 = 1852932833) B1852932833
theorem B2310911 : Blo 1539967 2310911 := bstep (se 1 (by rfl) ⟨1733183, by rfl⟩ : syracuseStep 2310911 = 3466367) B3466367
theorem B5850377 : Blo 1539967 5850377 := bstep (se 2 (by rfl) ⟨2193891, by rfl⟩ : syracuseStep 5850377 = 4387783) B4387783
theorem B11110439 : Blo 1539967 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B3901547 : Blo 1539967 3901547 := bstep (se 1 (by rfl) ⟨2926160, by rfl⟩ : syracuseStep 3901547 = 5852321) B5852321
theorem B3467375 : Blo 1539967 3467375 := bstep (se 1 (by rfl) ⟨2600531, by rfl⟩ : syracuseStep 3467375 = 5201063) B5201063
theorem B608160413 : Blo 1539967 608160413 := bstep (se 3 (by rfl) ⟨114030077, by rfl⟩ : syracuseStep 608160413 = 228060155) B228060155
theorem B11856617 : Blo 1539967 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B10546129 : Blo 1539967 10546129 := bstep (se 2 (by rfl) ⟨3954798, by rfl⟩ : syracuseStep 10546129 = 7909597) B7909597
theorem B133214543 : Blo 1539967 133214543 := bstep (se 1 (by rfl) ⟨99910907, by rfl⟩ : syracuseStep 133214543 = 199821815) B199821815
theorem B2965199 : Blo 1539967 2965199 := bstep (se 1 (by rfl) ⟨2223899, by rfl⟩ : syracuseStep 2965199 = 4447799) B4447799
theorem B90037993 : Blo 1539967 90037993 := bstep (se 2 (by rfl) ⟨33764247, by rfl⟩ : syracuseStep 90037993 = 67528495) B67528495
theorem B1540263 : Blo 1539967 1540263 := bstep (se 1 (by rfl) ⟨1155197, by rfl⟩ : syracuseStep 1540263 = 2310395) B2310395
theorem B88809695 : Blo 1539967 88809695 := bstep (se 1 (by rfl) ⟨66607271, by rfl⟩ : syracuseStep 88809695 = 133214543) B133214543
theorem B823525703 : Blo 1539967 823525703 := bstep (se 1 (by rfl) ⟨617644277, by rfl⟩ : syracuseStep 823525703 = 1235288555) B1235288555
theorem B1540607 : Blo 1539967 1540607 := bstep (se 1 (by rfl) ⟨1155455, by rfl⟩ : syracuseStep 1540607 = 2310911) B2310911
theorem B3900251 : Blo 1539967 3900251 := bstep (se 1 (by rfl) ⟨2925188, by rfl⟩ : syracuseStep 3900251 = 5850377) B5850377
theorem B7406959 : Blo 1539967 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B2311583 : Blo 1539967 2311583 := bstep (se 1 (by rfl) ⟨1733687, by rfl⟩ : syracuseStep 2311583 = 3467375) B3467375
theorem B405440275 : Blo 1539967 405440275 := bstep (se 1 (by rfl) ⟨304080206, by rfl⟩ : syracuseStep 405440275 = 608160413) B608160413
theorem B14061505 : Blo 1539967 14061505 := bstep (se 2 (by rfl) ⟨5273064, by rfl⟩ : syracuseStep 14061505 = 10546129) B10546129
theorem B2601031 : Blo 1539967 2601031 := bstep (se 1 (by rfl) ⟨1950773, by rfl⟩ : syracuseStep 2601031 = 3901547) B3901547
theorem B120050657 : Blo 1539967 120050657 := bstep (se 2 (by rfl) ⟨45018996, by rfl⟩ : syracuseStep 120050657 = 90037993) B90037993
theorem B7902623 : Blo 1539967 7902623 := bstep (se 1 (by rfl) ⟨5926967, by rfl⟩ : syracuseStep 7902623 = 11853935) B11853935
theorem B7904411 : Blo 1539967 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B31628789 : Blo 1539967 31628789 := bstep (se 5 (by rfl) ⟨1482599, by rfl⟩ : syracuseStep 31628789 = 2965199) B2965199
theorem B5268415 : Blo 1539967 5268415 := bstep (se 1 (by rfl) ⟨3951311, by rfl⟩ : syracuseStep 5268415 = 7902623) B7902623
theorem B1541055 : Blo 1539967 1541055 := bstep (se 1 (by rfl) ⟨1155791, by rfl⟩ : syracuseStep 1541055 = 2311583) B2311583
theorem B5269607 : Blo 1539967 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B3468041 : Blo 1539967 3468041 := bstep (se 2 (by rfl) ⟨1300515, by rfl⟩ : syracuseStep 3468041 = 2601031) B2601031
theorem B59206463 : Blo 1539967 59206463 := bstep (se 1 (by rfl) ⟨44404847, by rfl⟩ : syracuseStep 59206463 = 88809695) B88809695
theorem B2600167 : Blo 1539967 2600167 := bstep (se 1 (by rfl) ⟨1950125, by rfl⟩ : syracuseStep 2600167 = 3900251) B3900251
theorem B9875945 : Blo 1539967 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B540587033 : Blo 1539967 540587033 := bstep (se 2 (by rfl) ⟨202720137, by rfl⟩ : syracuseStep 540587033 = 405440275) B405440275
theorem B18748673 : Blo 1539967 18748673 := bstep (se 2 (by rfl) ⟨7030752, by rfl⟩ : syracuseStep 18748673 = 14061505) B14061505
theorem B549017135 : Blo 1539967 549017135 := bstep (se 1 (by rfl) ⟨411762851, by rfl⟩ : syracuseStep 549017135 = 823525703) B823525703
theorem B80033771 : Blo 1539967 80033771 := bstep (se 1 (by rfl) ⟨60025328, by rfl⟩ : syracuseStep 80033771 = 120050657) B120050657
theorem B21085859 : Blo 1539967 21085859 := bstep (se 1 (by rfl) ⟨15814394, by rfl⟩ : syracuseStep 21085859 = 31628789) B31628789
theorem B360391355 : Blo 1539967 360391355 := bstep (se 1 (by rfl) ⟨270293516, by rfl⟩ : syracuseStep 360391355 = 540587033) B540587033
theorem B366011423 : Blo 1539967 366011423 := bstep (se 1 (by rfl) ⟨274508567, by rfl⟩ : syracuseStep 366011423 = 549017135) B549017135
theorem B53355847 : Blo 1539967 53355847 := bstep (se 1 (by rfl) ⟨40016885, by rfl⟩ : syracuseStep 53355847 = 80033771) B80033771
theorem B3466889 : Blo 1539967 3466889 := bstep (se 2 (by rfl) ⟨1300083, by rfl⟩ : syracuseStep 3466889 = 2600167) B2600167
theorem B2312027 : Blo 1539967 2312027 := bstep (se 1 (by rfl) ⟨1734020, by rfl⟩ : syracuseStep 2312027 = 3468041) B3468041
theorem B39470975 : Blo 1539967 39470975 := bstep (se 1 (by rfl) ⟨29603231, by rfl⟩ : syracuseStep 39470975 = 59206463) B59206463
theorem B7024553 : Blo 1539967 7024553 := bstep (se 2 (by rfl) ⟨2634207, by rfl⟩ : syracuseStep 7024553 = 5268415) B5268415
theorem B12499115 : Blo 1539967 12499115 := bstep (se 1 (by rfl) ⟨9374336, by rfl⟩ : syracuseStep 12499115 = 18748673) B18748673
theorem B26335853 : Blo 1539967 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B3513071 : Blo 1539967 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B14057239 : Blo 1539967 14057239 := bstep (se 1 (by rfl) ⟨10542929, by rfl⟩ : syracuseStep 14057239 = 21085859) B21085859
theorem B244007615 : Blo 1539967 244007615 := bstep (se 1 (by rfl) ⟨183005711, by rfl⟩ : syracuseStep 244007615 = 366011423) B366011423
theorem B2311259 : Blo 1539967 2311259 := bstep (se 1 (by rfl) ⟨1733444, by rfl⟩ : syracuseStep 2311259 = 3466889) B3466889
theorem B1541351 : Blo 1539967 1541351 := bstep (se 1 (by rfl) ⟨1156013, by rfl⟩ : syracuseStep 1541351 = 2312027) B2312027
theorem B26313983 : Blo 1539967 26313983 := bstep (se 1 (by rfl) ⟨19735487, by rfl⟩ : syracuseStep 26313983 = 39470975) B39470975
theorem B17557235 : Blo 1539967 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B71141129 : Blo 1539967 71141129 := bstep (se 2 (by rfl) ⟨26677923, by rfl⟩ : syracuseStep 71141129 = 53355847) B53355847
theorem B4683035 : Blo 1539967 4683035 := bstep (se 1 (by rfl) ⟨3512276, by rfl⟩ : syracuseStep 4683035 = 7024553) B7024553
theorem B33330973 : Blo 1539967 33330973 := bstep (se 3 (by rfl) ⟨6249557, by rfl⟩ : syracuseStep 33330973 = 12499115) B12499115
theorem B240260903 : Blo 1539967 240260903 := bstep (se 1 (by rfl) ⟨180195677, by rfl⟩ : syracuseStep 240260903 = 360391355) B360391355
theorem B2342047 : Blo 1539967 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B18742985 : Blo 1539967 18742985 := bstep (se 2 (by rfl) ⟨7028619, by rfl⟩ : syracuseStep 18742985 = 14057239) B14057239
theorem B1540839 : Blo 1539967 1540839 := bstep (se 1 (by rfl) ⟨1155629, by rfl⟩ : syracuseStep 1540839 = 2311259) B2311259
theorem B3122023 : Blo 1539967 3122023 := bstep (se 1 (by rfl) ⟨2341517, by rfl⟩ : syracuseStep 3122023 = 4683035) B4683035
theorem B3122729 : Blo 1539967 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B12495323 : Blo 1539967 12495323 := bstep (se 1 (by rfl) ⟨9371492, by rfl⟩ : syracuseStep 12495323 = 18742985) B18742985
theorem B162671743 : Blo 1539967 162671743 := bstep (se 1 (by rfl) ⟨122003807, by rfl⟩ : syracuseStep 162671743 = 244007615) B244007615
theorem B17542655 : Blo 1539967 17542655 := bstep (se 1 (by rfl) ⟨13156991, by rfl⟩ : syracuseStep 17542655 = 26313983) B26313983
theorem B47427419 : Blo 1539967 47427419 := bstep (se 1 (by rfl) ⟨35570564, by rfl⟩ : syracuseStep 47427419 = 71141129) B71141129
theorem B160173935 : Blo 1539967 160173935 := bstep (se 1 (by rfl) ⟨120130451, by rfl⟩ : syracuseStep 160173935 = 240260903) B240260903
theorem B11704823 : Blo 1539967 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B44441297 : Blo 1539967 44441297 := bstep (se 2 (by rfl) ⟨16665486, by rfl⟩ : syracuseStep 44441297 = 33330973) B33330973
theorem B2081819 : Blo 1539967 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B4162697 : Blo 1539967 4162697 := bstep (se 2 (by rfl) ⟨1561011, by rfl⟩ : syracuseStep 4162697 = 3122023) B3122023
theorem B216895657 : Blo 1539967 216895657 := bstep (se 2 (by rfl) ⟨81335871, by rfl⟩ : syracuseStep 216895657 = 162671743) B162671743
theorem B7803215 : Blo 1539967 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B11695103 : Blo 1539967 11695103 := bstep (se 1 (by rfl) ⟨8771327, by rfl⟩ : syracuseStep 11695103 = 17542655) B17542655
theorem B29627531 : Blo 1539967 29627531 := bstep (se 1 (by rfl) ⟨22220648, by rfl⟩ : syracuseStep 29627531 = 44441297) B44441297
theorem B31618279 : Blo 1539967 31618279 := bstep (se 1 (by rfl) ⟨23713709, by rfl⟩ : syracuseStep 31618279 = 47427419) B47427419
theorem B8330215 : Blo 1539967 8330215 := bstep (se 1 (by rfl) ⟨6247661, by rfl⟩ : syracuseStep 8330215 = 12495323) B12495323
theorem B106782623 : Blo 1539967 106782623 := bstep (se 1 (by rfl) ⟨80086967, by rfl⟩ : syracuseStep 106782623 = 160173935) B160173935
theorem B289194209 : Blo 1539967 289194209 := bstep (se 2 (by rfl) ⟨108447828, by rfl⟩ : syracuseStep 289194209 = 216895657) B216895657
theorem B5202143 : Blo 1539967 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B19751687 : Blo 1539967 19751687 := bstep (se 1 (by rfl) ⟨14813765, by rfl⟩ : syracuseStep 19751687 = 29627531) B29627531
theorem B42157705 : Blo 1539967 42157705 := bstep (se 2 (by rfl) ⟨15809139, by rfl⟩ : syracuseStep 42157705 = 31618279) B31618279
theorem B5551517 : Blo 1539967 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B7796735 : Blo 1539967 7796735 := bstep (se 1 (by rfl) ⟨5847551, by rfl⟩ : syracuseStep 7796735 = 11695103) B11695103
theorem B2775131 : Blo 1539967 2775131 := bstep (se 1 (by rfl) ⟨2081348, by rfl⟩ : syracuseStep 2775131 = 4162697) B4162697
theorem B11106953 : Blo 1539967 11106953 := bstep (se 2 (by rfl) ⟨4165107, by rfl⟩ : syracuseStep 11106953 = 8330215) B8330215
theorem B71188415 : Blo 1539967 71188415 := bstep (se 1 (by rfl) ⟨53391311, by rfl⟩ : syracuseStep 71188415 = 106782623) B106782623
theorem B14804045 : Blo 1539967 14804045 := bstep (se 3 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 14804045 = 5551517) B5551517
theorem B47458943 : Blo 1539967 47458943 := bstep (se 1 (by rfl) ⟨35594207, by rfl⟩ : syracuseStep 47458943 = 71188415) B71188415
theorem B3468095 : Blo 1539967 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B13167791 : Blo 1539967 13167791 := bstep (se 1 (by rfl) ⟨9875843, by rfl⟩ : syracuseStep 13167791 = 19751687) B19751687
theorem B5197823 : Blo 1539967 5197823 := bstep (se 1 (by rfl) ⟨3898367, by rfl⟩ : syracuseStep 5197823 = 7796735) B7796735
theorem B56210273 : Blo 1539967 56210273 := bstep (se 2 (by rfl) ⟨21078852, by rfl⟩ : syracuseStep 56210273 = 42157705) B42157705
theorem B192796139 : Blo 1539967 192796139 := bstep (se 1 (by rfl) ⟨144597104, by rfl⟩ : syracuseStep 192796139 = 289194209) B289194209
theorem B1850087 : Blo 1539967 1850087 := bstep (se 1 (by rfl) ⟨1387565, by rfl⟩ : syracuseStep 1850087 = 2775131) B2775131
theorem B7404635 : Blo 1539967 7404635 := bstep (se 1 (by rfl) ⟨5553476, by rfl⟩ : syracuseStep 7404635 = 11106953) B11106953
theorem B514123037 : Blo 1539967 514123037 := bstep (se 3 (by rfl) ⟨96398069, by rfl⟩ : syracuseStep 514123037 = 192796139) B192796139
theorem B3465215 : Blo 1539967 3465215 := bstep (se 1 (by rfl) ⟨2598911, by rfl⟩ : syracuseStep 3465215 = 5197823) B5197823
theorem B31639295 : Blo 1539967 31639295 := bstep (se 1 (by rfl) ⟨23729471, by rfl⟩ : syracuseStep 31639295 = 47458943) B47458943
theorem B2312063 : Blo 1539967 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B4933565 : Blo 1539967 4933565 := bstep (se 3 (by rfl) ⟨925043, by rfl⟩ : syracuseStep 4933565 = 1850087) B1850087
theorem B19745693 : Blo 1539967 19745693 := bstep (se 3 (by rfl) ⟨3702317, by rfl⟩ : syracuseStep 19745693 = 7404635) B7404635
theorem B37473515 : Blo 1539967 37473515 := bstep (se 1 (by rfl) ⟨28105136, by rfl⟩ : syracuseStep 37473515 = 56210273) B56210273
theorem B8778527 : Blo 1539967 8778527 := bstep (se 1 (by rfl) ⟨6583895, by rfl⟩ : syracuseStep 8778527 = 13167791) B13167791
theorem B9869363 : Blo 1539967 9869363 := bstep (se 1 (by rfl) ⟨7402022, by rfl⟩ : syracuseStep 9869363 = 14804045) B14804045
theorem B1541375 : Blo 1539967 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B6579575 : Blo 1539967 6579575 := bstep (se 1 (by rfl) ⟨4934681, by rfl⟩ : syracuseStep 6579575 = 9869363) B9869363
theorem B84371453 : Blo 1539967 84371453 := bstep (se 3 (by rfl) ⟨15819647, by rfl⟩ : syracuseStep 84371453 = 31639295) B31639295
theorem B5852351 : Blo 1539967 5852351 := bstep (se 1 (by rfl) ⟨4389263, by rfl⟩ : syracuseStep 5852351 = 8778527) B8778527
theorem B342748691 : Blo 1539967 342748691 := bstep (se 1 (by rfl) ⟨257061518, by rfl⟩ : syracuseStep 342748691 = 514123037) B514123037
theorem B3289043 : Blo 1539967 3289043 := bstep (se 1 (by rfl) ⟨2466782, by rfl⟩ : syracuseStep 3289043 = 4933565) B4933565
theorem B24982343 : Blo 1539967 24982343 := bstep (se 1 (by rfl) ⟨18736757, by rfl⟩ : syracuseStep 24982343 = 37473515) B37473515
theorem B13163795 : Blo 1539967 13163795 := bstep (se 1 (by rfl) ⟨9872846, by rfl⟩ : syracuseStep 13163795 = 19745693) B19745693
theorem B2310143 : Blo 1539967 2310143 := bstep (se 1 (by rfl) ⟨1732607, by rfl⟩ : syracuseStep 2310143 = 3465215) B3465215
theorem B16654895 : Blo 1539967 16654895 := bstep (se 1 (by rfl) ⟨12491171, by rfl⟩ : syracuseStep 16654895 = 24982343) B24982343
theorem B56247635 : Blo 1539967 56247635 := bstep (se 1 (by rfl) ⟨42185726, by rfl⟩ : syracuseStep 56247635 = 84371453) B84371453
theorem B3901567 : Blo 1539967 3901567 := bstep (se 1 (by rfl) ⟨2926175, by rfl⟩ : syracuseStep 3901567 = 5852351) B5852351
theorem B8775863 : Blo 1539967 8775863 := bstep (se 1 (by rfl) ⟨6581897, by rfl⟩ : syracuseStep 8775863 = 13163795) B13163795
theorem B4386383 : Blo 1539967 4386383 := bstep (se 1 (by rfl) ⟨3289787, by rfl⟩ : syracuseStep 4386383 = 6579575) B6579575
theorem B8770781 : Blo 1539967 8770781 := bstep (se 3 (by rfl) ⟨1644521, by rfl⟩ : syracuseStep 8770781 = 3289043) B3289043
theorem B1540095 : Blo 1539967 1540095 := bstep (se 1 (by rfl) ⟨1155071, by rfl⟩ : syracuseStep 1540095 = 2310143) B2310143
theorem B228499127 : Blo 1539967 228499127 := bstep (se 1 (by rfl) ⟨171374345, by rfl⟩ : syracuseStep 228499127 = 342748691) B342748691
theorem B5202089 : Blo 1539967 5202089 := bstep (se 2 (by rfl) ⟨1950783, by rfl⟩ : syracuseStep 5202089 = 3901567) B3901567
theorem B5850575 : Blo 1539967 5850575 := bstep (se 1 (by rfl) ⟨4387931, by rfl⟩ : syracuseStep 5850575 = 8775863) B8775863
theorem B152332751 : Blo 1539967 152332751 := bstep (se 1 (by rfl) ⟨114249563, by rfl⟩ : syracuseStep 152332751 = 228499127) B228499127
theorem B11103263 : Blo 1539967 11103263 := bstep (se 1 (by rfl) ⟨8327447, by rfl⟩ : syracuseStep 11103263 = 16654895) B16654895
theorem B37498423 : Blo 1539967 37498423 := bstep (se 1 (by rfl) ⟨28123817, by rfl⟩ : syracuseStep 37498423 = 56247635) B56247635
theorem B5847187 : Blo 1539967 5847187 := bstep (se 1 (by rfl) ⟨4385390, by rfl⟩ : syracuseStep 5847187 = 8770781) B8770781
theorem B2924255 : Blo 1539967 2924255 := bstep (se 1 (by rfl) ⟨2193191, by rfl⟩ : syracuseStep 2924255 = 4386383) B4386383
theorem B3900383 : Blo 1539967 3900383 := bstep (se 1 (by rfl) ⟨2925287, by rfl⟩ : syracuseStep 3900383 = 5850575) B5850575
theorem B49997897 : Blo 1539967 49997897 := bstep (se 2 (by rfl) ⟨18749211, by rfl⟩ : syracuseStep 49997897 = 37498423) B37498423
theorem B3468059 : Blo 1539967 3468059 := bstep (se 1 (by rfl) ⟨2601044, by rfl⟩ : syracuseStep 3468059 = 5202089) B5202089
theorem B7402175 : Blo 1539967 7402175 := bstep (se 1 (by rfl) ⟨5551631, by rfl⟩ : syracuseStep 7402175 = 11103263) B11103263
theorem B7796249 : Blo 1539967 7796249 := bstep (se 2 (by rfl) ⟨2923593, by rfl⟩ : syracuseStep 7796249 = 5847187) B5847187
theorem B101555167 : Blo 1539967 101555167 := bstep (se 1 (by rfl) ⟨76166375, by rfl⟩ : syracuseStep 101555167 = 152332751) B152332751
theorem B1949503 : Blo 1539967 1949503 := bstep (se 1 (by rfl) ⟨1462127, by rfl⟩ : syracuseStep 1949503 = 2924255) B2924255
theorem B135406889 : Blo 1539967 135406889 := bstep (se 2 (by rfl) ⟨50777583, by rfl⟩ : syracuseStep 135406889 = 101555167) B101555167
theorem B2312039 : Blo 1539967 2312039 := bstep (se 1 (by rfl) ⟨1734029, by rfl⟩ : syracuseStep 2312039 = 3468059) B3468059
theorem B2599337 : Blo 1539967 2599337 := bstep (se 2 (by rfl) ⟨974751, by rfl⟩ : syracuseStep 2599337 = 1949503) B1949503
theorem B4934783 : Blo 1539967 4934783 := bstep (se 1 (by rfl) ⟨3701087, by rfl⟩ : syracuseStep 4934783 = 7402175) B7402175
theorem B2600255 : Blo 1539967 2600255 := bstep (se 1 (by rfl) ⟨1950191, by rfl⟩ : syracuseStep 2600255 = 3900383) B3900383
theorem B5197499 : Blo 1539967 5197499 := bstep (se 1 (by rfl) ⟨3898124, by rfl⟩ : syracuseStep 5197499 = 7796249) B7796249
theorem B33331931 : Blo 1539967 33331931 := bstep (se 1 (by rfl) ⟨24998948, by rfl⟩ : syracuseStep 33331931 = 49997897) B49997897
theorem B1541359 : Blo 1539967 1541359 := bstep (se 1 (by rfl) ⟨1156019, by rfl⟩ : syracuseStep 1541359 = 2312039) B2312039
theorem B13159421 : Blo 1539967 13159421 := bstep (se 3 (by rfl) ⟨2467391, by rfl⟩ : syracuseStep 13159421 = 4934783) B4934783
theorem B90271259 : Blo 1539967 90271259 := bstep (se 1 (by rfl) ⟨67703444, by rfl⟩ : syracuseStep 90271259 = 135406889) B135406889
theorem B1732891 : Blo 1539967 1732891 := bstep (se 1 (by rfl) ⟨1299668, by rfl⟩ : syracuseStep 1732891 = 2599337) B2599337
theorem B22221287 : Blo 1539967 22221287 := bstep (se 1 (by rfl) ⟨16665965, by rfl⟩ : syracuseStep 22221287 = 33331931) B33331931
theorem B1733503 : Blo 1539967 1733503 := bstep (se 1 (by rfl) ⟨1300127, by rfl⟩ : syracuseStep 1733503 = 2600255) B2600255
theorem B3464999 : Blo 1539967 3464999 := bstep (se 1 (by rfl) ⟨2598749, by rfl⟩ : syracuseStep 3464999 = 5197499) B5197499
theorem B2310521 : Blo 1539967 2310521 := bstep (se 2 (by rfl) ⟨866445, by rfl⟩ : syracuseStep 2310521 = 1732891) B1732891
theorem B2311337 : Blo 1539967 2311337 := bstep (se 2 (by rfl) ⟨866751, by rfl⟩ : syracuseStep 2311337 = 1733503) B1733503
theorem B60180839 : Blo 1539967 60180839 := bstep (se 1 (by rfl) ⟨45135629, by rfl⟩ : syracuseStep 60180839 = 90271259) B90271259
theorem B14814191 : Blo 1539967 14814191 := bstep (se 1 (by rfl) ⟨11110643, by rfl⟩ : syracuseStep 14814191 = 22221287) B22221287
theorem B8772947 : Blo 1539967 8772947 := bstep (se 1 (by rfl) ⟨6579710, by rfl⟩ : syracuseStep 8772947 = 13159421) B13159421
theorem B2309999 : Blo 1539967 2309999 := bstep (se 1 (by rfl) ⟨1732499, by rfl⟩ : syracuseStep 2309999 = 3464999) B3464999
theorem B1540347 : Blo 1539967 1540347 := bstep (se 1 (by rfl) ⟨1155260, by rfl⟩ : syracuseStep 1540347 = 2310521) B2310521
theorem B1540891 : Blo 1539967 1540891 := bstep (se 1 (by rfl) ⟨1155668, by rfl⟩ : syracuseStep 1540891 = 2311337) B2311337
theorem B40120559 : Blo 1539967 40120559 := bstep (se 1 (by rfl) ⟨30090419, by rfl⟩ : syracuseStep 40120559 = 60180839) B60180839
theorem B9876127 : Blo 1539967 9876127 := bstep (se 1 (by rfl) ⟨7407095, by rfl⟩ : syracuseStep 9876127 = 14814191) B14814191
theorem B5848631 : Blo 1539967 5848631 := bstep (se 1 (by rfl) ⟨4386473, by rfl⟩ : syracuseStep 5848631 = 8772947) B8772947
theorem B1539999 : Blo 1539967 1539999 := bstep (se 1 (by rfl) ⟨1154999, by rfl⟩ : syracuseStep 1539999 = 2309999) B2309999
theorem B26747039 : Blo 1539967 26747039 := bstep (se 1 (by rfl) ⟨20060279, by rfl⟩ : syracuseStep 26747039 = 40120559) B40120559
theorem B13168169 : Blo 1539967 13168169 := bstep (se 2 (by rfl) ⟨4938063, by rfl⟩ : syracuseStep 13168169 = 9876127) B9876127
theorem B3899087 : Blo 1539967 3899087 := bstep (se 1 (by rfl) ⟨2924315, by rfl⟩ : syracuseStep 3899087 = 5848631) B5848631
theorem B2599391 : Blo 1539967 2599391 := bstep (se 1 (by rfl) ⟨1949543, by rfl⟩ : syracuseStep 2599391 = 3899087) B3899087
theorem B8778779 : Blo 1539967 8778779 := bstep (se 1 (by rfl) ⟨6584084, by rfl⟩ : syracuseStep 8778779 = 13168169) B13168169
theorem B17831359 : Blo 1539967 17831359 := bstep (se 1 (by rfl) ⟨13373519, by rfl⟩ : syracuseStep 17831359 = 26747039) B26747039
theorem B5852519 : Blo 1539967 5852519 := bstep (se 1 (by rfl) ⟨4389389, by rfl⟩ : syracuseStep 5852519 = 8778779) B8778779
theorem B1732927 : Blo 1539967 1732927 := bstep (se 1 (by rfl) ⟨1299695, by rfl⟩ : syracuseStep 1732927 = 2599391) B2599391
theorem B95100581 : Blo 1539967 95100581 := bstep (se 4 (by rfl) ⟨8915679, by rfl⟩ : syracuseStep 95100581 = 17831359) B17831359
theorem B2310569 : Blo 1539967 2310569 := bstep (se 2 (by rfl) ⟨866463, by rfl⟩ : syracuseStep 2310569 = 1732927) B1732927
theorem B253601549 : Blo 1539967 253601549 := bstep (se 3 (by rfl) ⟨47550290, by rfl⟩ : syracuseStep 253601549 = 95100581) B95100581
theorem B3901679 : Blo 1539967 3901679 := bstep (se 1 (by rfl) ⟨2926259, by rfl⟩ : syracuseStep 3901679 = 5852519) B5852519
theorem B1540379 : Blo 1539967 1540379 := bstep (se 1 (by rfl) ⟨1155284, by rfl⟩ : syracuseStep 1540379 = 2310569) B2310569
theorem B169067699 : Blo 1539967 169067699 := bstep (se 1 (by rfl) ⟨126800774, by rfl⟩ : syracuseStep 169067699 = 253601549) B253601549
theorem B2601119 : Blo 1539967 2601119 := bstep (se 1 (by rfl) ⟨1950839, by rfl⟩ : syracuseStep 2601119 = 3901679) B3901679
theorem B1734079 : Blo 1539967 1734079 := bstep (se 1 (by rfl) ⟨1300559, by rfl⟩ : syracuseStep 1734079 = 2601119) B2601119
theorem B112711799 : Blo 1539967 112711799 := bstep (se 1 (by rfl) ⟨84533849, by rfl⟩ : syracuseStep 112711799 = 169067699) B169067699
theorem B2312105 : Blo 1539967 2312105 := bstep (se 2 (by rfl) ⟨867039, by rfl⟩ : syracuseStep 2312105 = 1734079) B1734079
theorem B75141199 : Blo 1539967 75141199 := bstep (se 1 (by rfl) ⟨56355899, by rfl⟩ : syracuseStep 75141199 = 112711799) B112711799
theorem B100188265 : Blo 1539967 100188265 := bstep (se 2 (by rfl) ⟨37570599, by rfl⟩ : syracuseStep 100188265 = 75141199) B75141199
theorem B1541403 : Blo 1539967 1541403 := bstep (se 1 (by rfl) ⟨1156052, by rfl⟩ : syracuseStep 1541403 = 2312105) B2312105
theorem B133584353 : Blo 1539967 133584353 := bstep (se 2 (by rfl) ⟨50094132, by rfl⟩ : syracuseStep 133584353 = 100188265) B100188265
theorem B89056235 : Blo 1539967 89056235 := bstep (se 1 (by rfl) ⟨66792176, by rfl⟩ : syracuseStep 89056235 = 133584353) B133584353
theorem B59370823 : Blo 1539967 59370823 := bstep (se 1 (by rfl) ⟨44528117, by rfl⟩ : syracuseStep 59370823 = 89056235) B89056235
theorem B79161097 : Blo 1539967 79161097 := bstep (se 2 (by rfl) ⟨29685411, by rfl⟩ : syracuseStep 79161097 = 59370823) B59370823
theorem B105548129 : Blo 1539967 105548129 := bstep (se 2 (by rfl) ⟨39580548, by rfl⟩ : syracuseStep 105548129 = 79161097) B79161097
theorem B70365419 : Blo 1539967 70365419 := bstep (se 1 (by rfl) ⟨52774064, by rfl⟩ : syracuseStep 70365419 = 105548129) B105548129
theorem B46910279 : Blo 1539967 46910279 := bstep (se 1 (by rfl) ⟨35182709, by rfl⟩ : syracuseStep 46910279 = 70365419) B70365419
theorem B125094077 : Blo 1539967 125094077 := bstep (se 3 (by rfl) ⟨23455139, by rfl⟩ : syracuseStep 125094077 = 46910279) B46910279
theorem B83396051 : Blo 1539967 83396051 := bstep (se 1 (by rfl) ⟨62547038, by rfl⟩ : syracuseStep 83396051 = 125094077) B125094077
theorem B55597367 : Blo 1539967 55597367 := bstep (se 1 (by rfl) ⟨41698025, by rfl⟩ : syracuseStep 55597367 = 83396051) B83396051
theorem B37064911 : Blo 1539967 37064911 := bstep (se 1 (by rfl) ⟨27798683, by rfl⟩ : syracuseStep 37064911 = 55597367) B55597367
theorem B49419881 : Blo 1539967 49419881 := bstep (se 2 (by rfl) ⟨18532455, by rfl⟩ : syracuseStep 49419881 = 37064911) B37064911
theorem B32946587 : Blo 1539967 32946587 := bstep (se 1 (by rfl) ⟨24709940, by rfl⟩ : syracuseStep 32946587 = 49419881) B49419881
theorem B21964391 : Blo 1539967 21964391 := bstep (se 1 (by rfl) ⟨16473293, by rfl⟩ : syracuseStep 21964391 = 32946587) B32946587
theorem B14642927 : Blo 1539967 14642927 := bstep (se 1 (by rfl) ⟨10982195, by rfl⟩ : syracuseStep 14642927 = 21964391) B21964391
theorem B9761951 : Blo 1539967 9761951 := bstep (se 1 (by rfl) ⟨7321463, by rfl⟩ : syracuseStep 9761951 = 14642927) B14642927
theorem B6507967 : Blo 1539967 6507967 := bstep (se 1 (by rfl) ⟨4880975, by rfl⟩ : syracuseStep 6507967 = 9761951) B9761951
theorem B8677289 : Blo 1539967 8677289 := bstep (se 2 (by rfl) ⟨3253983, by rfl⟩ : syracuseStep 8677289 = 6507967) B6507967
theorem B5784859 : Blo 1539967 5784859 := bstep (se 1 (by rfl) ⟨4338644, by rfl⟩ : syracuseStep 5784859 = 8677289) B8677289
theorem B7713145 : Blo 1539967 7713145 := bstep (se 2 (by rfl) ⟨2892429, by rfl⟩ : syracuseStep 7713145 = 5784859) B5784859
theorem B10284193 : Blo 1539967 10284193 := bstep (se 2 (by rfl) ⟨3856572, by rfl⟩ : syracuseStep 10284193 = 7713145) B7713145
theorem B13712257 : Blo 1539967 13712257 := bstep (se 2 (by rfl) ⟨5142096, by rfl⟩ : syracuseStep 13712257 = 10284193) B10284193
theorem B18283009 : Blo 1539967 18283009 := bstep (se 2 (by rfl) ⟨6856128, by rfl⟩ : syracuseStep 18283009 = 13712257) B13712257
theorem B24377345 : Blo 1539967 24377345 := bstep (se 2 (by rfl) ⟨9141504, by rfl⟩ : syracuseStep 24377345 = 18283009) B18283009
theorem B16251563 : Blo 1539967 16251563 := bstep (se 1 (by rfl) ⟨12188672, by rfl⟩ : syracuseStep 16251563 = 24377345) B24377345
theorem B43337501 : Blo 1539967 43337501 := bstep (se 3 (by rfl) ⟨8125781, by rfl⟩ : syracuseStep 43337501 = 16251563) B16251563
theorem B28891667 : Blo 1539967 28891667 := bstep (se 1 (by rfl) ⟨21668750, by rfl⟩ : syracuseStep 28891667 = 43337501) B43337501
theorem B19261111 : Blo 1539967 19261111 := bstep (se 1 (by rfl) ⟨14445833, by rfl⟩ : syracuseStep 19261111 = 28891667) B28891667
theorem B25681481 : Blo 1539967 25681481 := bstep (se 2 (by rfl) ⟨9630555, by rfl⟩ : syracuseStep 25681481 = 19261111) B19261111
theorem B17120987 : Blo 1539967 17120987 := bstep (se 1 (by rfl) ⟨12840740, by rfl⟩ : syracuseStep 17120987 = 25681481) B25681481
theorem B11413991 : Blo 1539967 11413991 := bstep (se 1 (by rfl) ⟨8560493, by rfl⟩ : syracuseStep 11413991 = 17120987) B17120987
theorem B30437309 : Blo 1539967 30437309 := bstep (se 3 (by rfl) ⟨5706995, by rfl⟩ : syracuseStep 30437309 = 11413991) B11413991
theorem B20291539 : Blo 1539967 20291539 := bstep (se 1 (by rfl) ⟨15218654, by rfl⟩ : syracuseStep 20291539 = 30437309) B30437309
theorem B27055385 : Blo 1539967 27055385 := bstep (se 2 (by rfl) ⟨10145769, by rfl⟩ : syracuseStep 27055385 = 20291539) B20291539
theorem B18036923 : Blo 1539967 18036923 := bstep (se 1 (by rfl) ⟨13527692, by rfl⟩ : syracuseStep 18036923 = 27055385) B27055385
theorem B48098461 : Blo 1539967 48098461 := bstep (se 3 (by rfl) ⟨9018461, by rfl⟩ : syracuseStep 48098461 = 18036923) B18036923
theorem B64131281 : Blo 1539967 64131281 := bstep (se 2 (by rfl) ⟨24049230, by rfl⟩ : syracuseStep 64131281 = 48098461) B48098461
theorem B42754187 : Blo 1539967 42754187 := bstep (se 1 (by rfl) ⟨32065640, by rfl⟩ : syracuseStep 42754187 = 64131281) B64131281
theorem B114011165 : Blo 1539967 114011165 := bstep (se 3 (by rfl) ⟨21377093, by rfl⟩ : syracuseStep 114011165 = 42754187) B42754187
theorem B76007443 : Blo 1539967 76007443 := bstep (se 1 (by rfl) ⟨57005582, by rfl⟩ : syracuseStep 76007443 = 114011165) B114011165
theorem B101343257 : Blo 1539967 101343257 := bstep (se 2 (by rfl) ⟨38003721, by rfl⟩ : syracuseStep 101343257 = 76007443) B76007443
theorem B67562171 : Blo 1539967 67562171 := bstep (se 1 (by rfl) ⟨50671628, by rfl⟩ : syracuseStep 67562171 = 101343257) B101343257
theorem B45041447 : Blo 1539967 45041447 := bstep (se 1 (by rfl) ⟨33781085, by rfl⟩ : syracuseStep 45041447 = 67562171) B67562171
theorem B30027631 : Blo 1539967 30027631 := bstep (se 1 (by rfl) ⟨22520723, by rfl⟩ : syracuseStep 30027631 = 45041447) B45041447
theorem B40036841 : Blo 1539967 40036841 := bstep (se 2 (by rfl) ⟨15013815, by rfl⟩ : syracuseStep 40036841 = 30027631) B30027631
theorem B26691227 : Blo 1539967 26691227 := bstep (se 1 (by rfl) ⟨20018420, by rfl⟩ : syracuseStep 26691227 = 40036841) B40036841
theorem B17794151 : Blo 1539967 17794151 := bstep (se 1 (by rfl) ⟨13345613, by rfl⟩ : syracuseStep 17794151 = 26691227) B26691227
theorem B11862767 : Blo 1539967 11862767 := bstep (se 1 (by rfl) ⟨8897075, by rfl⟩ : syracuseStep 11862767 = 17794151) B17794151
theorem B7908511 : Blo 1539967 7908511 := bstep (se 1 (by rfl) ⟨5931383, by rfl⟩ : syracuseStep 7908511 = 11862767) B11862767
theorem B10544681 : Blo 1539967 10544681 := bstep (se 2 (by rfl) ⟨3954255, by rfl⟩ : syracuseStep 10544681 = 7908511) B7908511
theorem B28119149 : Blo 1539967 28119149 := bstep (se 3 (by rfl) ⟨5272340, by rfl⟩ : syracuseStep 28119149 = 10544681) B10544681
theorem B18746099 : Blo 1539967 18746099 := bstep (se 1 (by rfl) ⟨14059574, by rfl⟩ : syracuseStep 18746099 = 28119149) B28119149
theorem B12497399 : Blo 1539967 12497399 := bstep (se 1 (by rfl) ⟨9373049, by rfl⟩ : syracuseStep 12497399 = 18746099) B18746099
theorem B8331599 : Blo 1539967 8331599 := bstep (se 1 (by rfl) ⟨6248699, by rfl⟩ : syracuseStep 8331599 = 12497399) B12497399
theorem B22217597 : Blo 1539967 22217597 := bstep (se 3 (by rfl) ⟨4165799, by rfl⟩ : syracuseStep 22217597 = 8331599) B8331599
theorem B14811731 : Blo 1539967 14811731 := bstep (se 1 (by rfl) ⟨11108798, by rfl⟩ : syracuseStep 14811731 = 22217597) B22217597
theorem B9874487 : Blo 1539967 9874487 := bstep (se 1 (by rfl) ⟨7405865, by rfl⟩ : syracuseStep 9874487 = 14811731) B14811731
theorem B6582991 : Blo 1539967 6582991 := bstep (se 1 (by rfl) ⟨4937243, by rfl⟩ : syracuseStep 6582991 = 9874487) B9874487
theorem B8777321 : Blo 1539967 8777321 := bstep (se 2 (by rfl) ⟨3291495, by rfl⟩ : syracuseStep 8777321 = 6582991) B6582991
theorem B5851547 : Blo 1539967 5851547 := bstep (se 1 (by rfl) ⟨4388660, by rfl⟩ : syracuseStep 5851547 = 8777321) B8777321
theorem B3901031 : Blo 1539967 3901031 := bstep (se 1 (by rfl) ⟨2925773, by rfl⟩ : syracuseStep 3901031 = 5851547) B5851547
theorem B2600687 : Blo 1539967 2600687 := bstep (se 1 (by rfl) ⟨1950515, by rfl⟩ : syracuseStep 2600687 = 3901031) B3901031
theorem B1733791 : Blo 1539967 1733791 := bstep (se 1 (by rfl) ⟨1300343, by rfl⟩ : syracuseStep 1733791 = 2600687) B2600687
theorem B2311721 : Blo 1539967 2311721 := bstep (se 2 (by rfl) ⟨866895, by rfl⟩ : syracuseStep 2311721 = 1733791) B1733791
theorem B1541147 : Blo 1539967 1541147 := bstep (se 1 (by rfl) ⟨1155860, by rfl⟩ : syracuseStep 1541147 = 2311721) B2311721

theorem C0 (j : ℕ) (h1 : 384991 ≤ j) (h2 : j ≤ 385366) : Blo 1539967 (4 * j + 3) := by
  interval_cases j
  · exact B1539967
  · exact B1539971
  · exact B1539975
  · exact B1539979
  · exact B1539983
  · exact B1539987
  · exact B1539991
  · exact B1539995
  · exact B1539999
  · exact B1540003
  · exact B1540007
  · exact B1540011
  · exact B1540015
  · exact B1540019
  · exact B1540023
  · exact B1540027
  · exact B1540031
  · exact B1540035
  · exact B1540039
  · exact B1540043
  · exact B1540047
  · exact B1540051
  · exact B1540055
  · exact B1540059
  · exact B1540063
  · exact B1540067
  · exact B1540071
  · exact B1540075
  · exact B1540079
  · exact B1540083
  · exact B1540087
  · exact B1540091
  · exact B1540095
  · exact B1540099
  · exact B1540103
  · exact B1540107
  · exact B1540111
  · exact B1540115
  · exact B1540119
  · exact B1540123
  · exact B1540127
  · exact B1540131
  · exact B1540135
  · exact B1540139
  · exact B1540143
  · exact B1540147
  · exact B1540151
  · exact B1540155
  · exact B1540159
  · exact B1540163
  · exact B1540167
  · exact B1540171
  · exact B1540175
  · exact B1540179
  · exact B1540183
  · exact B1540187
  · exact B1540191
  · exact B1540195
  · exact B1540199
  · exact B1540203
  · exact B1540207
  · exact B1540211
  · exact B1540215
  · exact B1540219
  · exact B1540223
  · exact B1540227
  · exact B1540231
  · exact B1540235
  · exact B1540239
  · exact B1540243
  · exact B1540247
  · exact B1540251
  · exact B1540255
  · exact B1540259
  · exact B1540263
  · exact B1540267
  · exact B1540271
  · exact B1540275
  · exact B1540279
  · exact B1540283
  · exact B1540287
  · exact B1540291
  · exact B1540295
  · exact B1540299
  · exact B1540303
  · exact B1540307
  · exact B1540311
  · exact B1540315
  · exact B1540319
  · exact B1540323
  · exact B1540327
  · exact B1540331
  · exact B1540335
  · exact B1540339
  · exact B1540343
  · exact B1540347
  · exact B1540351
  · exact B1540355
  · exact B1540359
  · exact B1540363
  · exact B1540367
  · exact B1540371
  · exact B1540375
  · exact B1540379
  · exact B1540383
  · exact B1540387
  · exact B1540391
  · exact B1540395
  · exact B1540399
  · exact B1540403
  · exact B1540407
  · exact B1540411
  · exact B1540415
  · exact B1540419
  · exact B1540423
  · exact B1540427
  · exact B1540431
  · exact B1540435
  · exact B1540439
  · exact B1540443
  · exact B1540447
  · exact B1540451
  · exact B1540455
  · exact B1540459
  · exact B1540463
  · exact B1540467
  · exact B1540471
  · exact B1540475
  · exact B1540479
  · exact B1540483
  · exact B1540487
  · exact B1540491
  · exact B1540495
  · exact B1540499
  · exact B1540503
  · exact B1540507
  · exact B1540511
  · exact B1540515
  · exact B1540519
  · exact B1540523
  · exact B1540527
  · exact B1540531
  · exact B1540535
  · exact B1540539
  · exact B1540543
  · exact B1540547
  · exact B1540551
  · exact B1540555
  · exact B1540559
  · exact B1540563
  · exact B1540567
  · exact B1540571
  · exact B1540575
  · exact B1540579
  · exact B1540583
  · exact B1540587
  · exact B1540591
  · exact B1540595
  · exact B1540599
  · exact B1540603
  · exact B1540607
  · exact B1540611
  · exact B1540615
  · exact B1540619
  · exact B1540623
  · exact B1540627
  · exact B1540631
  · exact B1540635
  · exact B1540639
  · exact B1540643
  · exact B1540647
  · exact B1540651
  · exact B1540655
  · exact B1540659
  · exact B1540663
  · exact B1540667
  · exact B1540671
  · exact B1540675
  · exact B1540679
  · exact B1540683
  · exact B1540687
  · exact B1540691
  · exact B1540695
  · exact B1540699
  · exact B1540703
  · exact B1540707
  · exact B1540711
  · exact B1540715
  · exact B1540719
  · exact B1540723
  · exact B1540727
  · exact B1540731
  · exact B1540735
  · exact B1540739
  · exact B1540743
  · exact B1540747
  · exact B1540751
  · exact B1540755
  · exact B1540759
  · exact B1540763
  · exact B1540767
  · exact B1540771
  · exact B1540775
  · exact B1540779
  · exact B1540783
  · exact B1540787
  · exact B1540791
  · exact B1540795
  · exact B1540799
  · exact B1540803
  · exact B1540807
  · exact B1540811
  · exact B1540815
  · exact B1540819
  · exact B1540823
  · exact B1540827
  · exact B1540831
  · exact B1540835
  · exact B1540839
  · exact B1540843
  · exact B1540847
  · exact B1540851
  · exact B1540855
  · exact B1540859
  · exact B1540863
  · exact B1540867
  · exact B1540871
  · exact B1540875
  · exact B1540879
  · exact B1540883
  · exact B1540887
  · exact B1540891
  · exact B1540895
  · exact B1540899
  · exact B1540903
  · exact B1540907
  · exact B1540911
  · exact B1540915
  · exact B1540919
  · exact B1540923
  · exact B1540927
  · exact B1540931
  · exact B1540935
  · exact B1540939
  · exact B1540943
  · exact B1540947
  · exact B1540951
  · exact B1540955
  · exact B1540959
  · exact B1540963
  · exact B1540967
  · exact B1540971
  · exact B1540975
  · exact B1540979
  · exact B1540983
  · exact B1540987
  · exact B1540991
  · exact B1540995
  · exact B1540999
  · exact B1541003
  · exact B1541007
  · exact B1541011
  · exact B1541015
  · exact B1541019
  · exact B1541023
  · exact B1541027
  · exact B1541031
  · exact B1541035
  · exact B1541039
  · exact B1541043
  · exact B1541047
  · exact B1541051
  · exact B1541055
  · exact B1541059
  · exact B1541063
  · exact B1541067
  · exact B1541071
  · exact B1541075
  · exact B1541079
  · exact B1541083
  · exact B1541087
  · exact B1541091
  · exact B1541095
  · exact B1541099
  · exact B1541103
  · exact B1541107
  · exact B1541111
  · exact B1541115
  · exact B1541119
  · exact B1541123
  · exact B1541127
  · exact B1541131
  · exact B1541135
  · exact B1541139
  · exact B1541143
  · exact B1541147
  · exact B1541151
  · exact B1541155
  · exact B1541159
  · exact B1541163
  · exact B1541167
  · exact B1541171
  · exact B1541175
  · exact B1541179
  · exact B1541183
  · exact B1541187
  · exact B1541191
  · exact B1541195
  · exact B1541199
  · exact B1541203
  · exact B1541207
  · exact B1541211
  · exact B1541215
  · exact B1541219
  · exact B1541223
  · exact B1541227
  · exact B1541231
  · exact B1541235
  · exact B1541239
  · exact B1541243
  · exact B1541247
  · exact B1541251
  · exact B1541255
  · exact B1541259
  · exact B1541263
  · exact B1541267
  · exact B1541271
  · exact B1541275
  · exact B1541279
  · exact B1541283
  · exact B1541287
  · exact B1541291
  · exact B1541295
  · exact B1541299
  · exact B1541303
  · exact B1541307
  · exact B1541311
  · exact B1541315
  · exact B1541319
  · exact B1541323
  · exact B1541327
  · exact B1541331
  · exact B1541335
  · exact B1541339
  · exact B1541343
  · exact B1541347
  · exact B1541351
  · exact B1541355
  · exact B1541359
  · exact B1541363
  · exact B1541367
  · exact B1541371
  · exact B1541375
  · exact B1541379
  · exact B1541383
  · exact B1541387
  · exact B1541391
  · exact B1541395
  · exact B1541399
  · exact B1541403
  · exact B1541407
  · exact B1541411
  · exact B1541415
  · exact B1541419
  · exact B1541423
  · exact B1541427
  · exact B1541431
  · exact B1541435
  · exact B1541439
  · exact B1541443
  · exact B1541447
  · exact B1541451
  · exact B1541455
  · exact B1541459
  · exact B1541463
  · exact B1541467

theorem solution (m : ℕ) (hlo : 1539967 ≤ m) (hhi : m ≤ 1541467) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 384991 ≤ j := by omega
    have hj2 : j ≤ 385366 := by omega
    have hb : Blo 1539967 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
