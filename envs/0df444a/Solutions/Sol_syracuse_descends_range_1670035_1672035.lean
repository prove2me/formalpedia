-- Prove2me | solution 1 for syracuse_descends_range_1670035_1672035
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:20:48.883733+00:00
-- url     : https://prove2.me/submissions/d808b3e1-1a00-41d3-96e4-ae35f83fc2a4

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


theorem B2506757 : Blo 1670035 2506757 := bbase (se 4 (by rfl) ⟨235008, by rfl⟩ : syracuseStep 2506757 = 470017) (by norm_num)
theorem B4759573 : Blo 1670035 4759573 := bbase (se 6 (by rfl) ⟨111552, by rfl⟩ : syracuseStep 4759573 = 223105) (by norm_num)
theorem B2506781 : Blo 1670035 2506781 := bbase (se 3 (by rfl) ⟨470021, by rfl⟩ : syracuseStep 2506781 = 940043) (by norm_num)
theorem B3760181 : Blo 1670035 3760181 := bbase (se 5 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 3760181 = 352517) (by norm_num)
theorem B2506805 : Blo 1670035 2506805 := bbase (se 5 (by rfl) ⟨117506, by rfl⟩ : syracuseStep 2506805 = 235013) (by norm_num)
theorem B2007109 : Blo 1670035 2007109 := bbase (se 4 (by rfl) ⟨188166, by rfl⟩ : syracuseStep 2007109 = 376333) (by norm_num)
theorem B2506829 : Blo 1670035 2506829 := bbase (se 3 (by rfl) ⟨470030, by rfl⟩ : syracuseStep 2506829 = 940061) (by norm_num)
theorem B2506853 : Blo 1670035 2506853 := bbase (se 4 (by rfl) ⟨235017, by rfl⟩ : syracuseStep 2506853 = 470035) (by norm_num)
theorem B3760253 : Blo 1670035 3760253 := bbase (se 3 (by rfl) ⟨705047, by rfl⟩ : syracuseStep 3760253 = 1410095) (by norm_num)
theorem B2506877 : Blo 1670035 2506877 := bbase (se 3 (by rfl) ⟨470039, by rfl⟩ : syracuseStep 2506877 = 940079) (by norm_num)
theorem B2506901 : Blo 1670035 2506901 := bbase (se 6 (by rfl) ⟨58755, by rfl⟩ : syracuseStep 2506901 = 117511) (by norm_num)
theorem B7135397 : Blo 1670035 7135397 := bbase (se 4 (by rfl) ⟨668943, by rfl⟩ : syracuseStep 7135397 = 1337887) (by norm_num)
theorem B2113705 : Blo 1670035 2113705 := bbase (se 2 (by rfl) ⟨792639, by rfl⟩ : syracuseStep 2113705 = 1585279) (by norm_num)
theorem B2506925 : Blo 1670035 2506925 := bbase (se 3 (by rfl) ⟨470048, by rfl⟩ : syracuseStep 2506925 = 940097) (by norm_num)
theorem B8028341 : Blo 1670035 8028341 := bbase (se 5 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 8028341 = 752657) (by norm_num)
theorem B3760325 : Blo 1670035 3760325 := bbase (se 4 (by rfl) ⟨352530, by rfl⟩ : syracuseStep 3760325 = 705061) (by norm_num)
theorem B2506949 : Blo 1670035 2506949 := bbase (se 4 (by rfl) ⟨235026, by rfl⟩ : syracuseStep 2506949 = 470053) (by norm_num)
theorem B2818253 : Blo 1670035 2818253 := bbase (se 3 (by rfl) ⟨528422, by rfl⟩ : syracuseStep 2818253 = 1056845) (by norm_num)
theorem B2506973 : Blo 1670035 2506973 := bbase (se 3 (by rfl) ⟨470057, by rfl⟩ : syracuseStep 2506973 = 940115) (by norm_num)
theorem B2506997 : Blo 1670035 2506997 := bbase (se 5 (by rfl) ⟨117515, by rfl⟩ : syracuseStep 2506997 = 235031) (by norm_num)
theorem B3170573 : Blo 1670035 3170573 := bbase (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) (by norm_num)
theorem B3760397 : Blo 1670035 3760397 := bbase (se 3 (by rfl) ⟨705074, by rfl⟩ : syracuseStep 3760397 = 1410149) (by norm_num)
theorem B2507021 : Blo 1670035 2507021 := bbase (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) (by norm_num)
theorem B4227349 : Blo 1670035 4227349 := bbase (se 6 (by rfl) ⟨99078, by rfl⟩ : syracuseStep 4227349 = 198157) (by norm_num)
theorem B2507045 : Blo 1670035 2507045 := bbase (se 4 (by rfl) ⟨235035, by rfl⟩ : syracuseStep 2507045 = 470071) (by norm_num)
theorem B2539829 : Blo 1670035 2539829 := bbase (se 5 (by rfl) ⟨119054, by rfl⟩ : syracuseStep 2539829 = 238109) (by norm_num)
theorem B2507069 : Blo 1670035 2507069 := bbase (se 3 (by rfl) ⟨470075, by rfl⟩ : syracuseStep 2507069 = 940151) (by norm_num)
theorem B2818381 : Blo 1670035 2818381 := bbase (se 3 (by rfl) ⟨528446, by rfl⟩ : syracuseStep 2818381 = 1056893) (by norm_num)
theorem B6340949 : Blo 1670035 6340949 := bbase (se 10 (by rfl) ⟨9288, by rfl⟩ : syracuseStep 6340949 = 18577) (by norm_num)
theorem B2113877 : Blo 1670035 2113877 := bbase (se 10 (by rfl) ⟨3096, by rfl⟩ : syracuseStep 2113877 = 6193) (by norm_num)
theorem B3760469 : Blo 1670035 3760469 := bbase (se 10 (by rfl) ⟨5508, by rfl⟩ : syracuseStep 3760469 = 11017) (by norm_num)
theorem B2507093 : Blo 1670035 2507093 := bbase (se 10 (by rfl) ⟨3672, by rfl⟩ : syracuseStep 2507093 = 7345) (by norm_num)
theorem B2507117 : Blo 1670035 2507117 := bbase (se 3 (by rfl) ⟨470084, by rfl⟩ : syracuseStep 2507117 = 940169) (by norm_num)
theorem B4227461 : Blo 1670035 4227461 := bbase (se 4 (by rfl) ⟨396324, by rfl⟩ : syracuseStep 4227461 = 792649) (by norm_num)
theorem B2507141 : Blo 1670035 2507141 := bbase (se 4 (by rfl) ⟨235044, by rfl⟩ : syracuseStep 2507141 = 470089) (by norm_num)
theorem B2113933 : Blo 1670035 2113933 := bbase (se 3 (by rfl) ⟨396362, by rfl⟩ : syracuseStep 2113933 = 792725) (by norm_num)
theorem B3760541 : Blo 1670035 3760541 := bbase (se 3 (by rfl) ⟨705101, by rfl⟩ : syracuseStep 3760541 = 1410203) (by norm_num)
theorem B2507165 : Blo 1670035 2507165 := bbase (se 3 (by rfl) ⟨470093, by rfl⟩ : syracuseStep 2507165 = 940187) (by norm_num)
theorem B2818469 : Blo 1670035 2818469 := bbase (se 4 (by rfl) ⟨264231, by rfl⟩ : syracuseStep 2818469 = 528463) (by norm_num)
theorem B2507189 : Blo 1670035 2507189 := bbase (se 5 (by rfl) ⟨117524, by rfl⟩ : syracuseStep 2507189 = 235049) (by norm_num)
theorem B2507213 : Blo 1670035 2507213 := bbase (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) (by norm_num)
theorem B3760613 : Blo 1670035 3760613 := bbase (se 4 (by rfl) ⟨352557, by rfl⟩ : syracuseStep 3760613 = 705115) (by norm_num)
theorem B2507237 : Blo 1670035 2507237 := bbase (se 4 (by rfl) ⟨235053, by rfl⟩ : syracuseStep 2507237 = 470107) (by norm_num)
theorem B2114029 : Blo 1670035 2114029 := bbase (se 3 (by rfl) ⟨396380, by rfl⟩ : syracuseStep 2114029 = 792761) (by norm_num)
theorem B2507261 : Blo 1670035 2507261 := bbase (se 3 (by rfl) ⟨470111, by rfl⟩ : syracuseStep 2507261 = 940223) (by norm_num)
theorem B4514309 : Blo 1670035 4514309 := bbase (se 4 (by rfl) ⟨423216, by rfl⟩ : syracuseStep 4514309 = 846433) (by norm_num)
theorem B9511445 : Blo 1670035 9511445 := bbase (se 6 (by rfl) ⟨222924, by rfl⟩ : syracuseStep 9511445 = 445849) (by norm_num)
theorem B28557845 : Blo 1670035 28557845 := bbase (se 6 (by rfl) ⟨669324, by rfl⟩ : syracuseStep 28557845 = 1338649) (by norm_num)
theorem B2507285 : Blo 1670035 2507285 := bbase (se 6 (by rfl) ⟨58764, by rfl⟩ : syracuseStep 2507285 = 117529) (by norm_num)
theorem B2818597 : Blo 1670035 2818597 := bbase (se 4 (by rfl) ⟨264243, by rfl⟩ : syracuseStep 2818597 = 528487) (by norm_num)
theorem B3760685 : Blo 1670035 3760685 := bbase (se 3 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 3760685 = 1410257) (by norm_num)
theorem B2507309 : Blo 1670035 2507309 := bbase (se 3 (by rfl) ⟨470120, by rfl⟩ : syracuseStep 2507309 = 940241) (by norm_num)
theorem B4071989 : Blo 1670035 4071989 := bbase (se 5 (by rfl) ⟨190874, by rfl⟩ : syracuseStep 4071989 = 381749) (by norm_num)
theorem B4227653 : Blo 1670035 4227653 := bbase (se 4 (by rfl) ⟨396342, by rfl⟩ : syracuseStep 4227653 = 792685) (by norm_num)
theorem B2507333 : Blo 1670035 2507333 := bbase (se 4 (by rfl) ⟨235062, by rfl⟩ : syracuseStep 2507333 = 470125) (by norm_num)
theorem B1884749 : Blo 1670035 1884749 := bbase (se 3 (by rfl) ⟨353390, by rfl⟩ : syracuseStep 1884749 = 706781) (by norm_num)
theorem B2507357 : Blo 1670035 2507357 := bbase (se 3 (by rfl) ⟨470129, by rfl⟩ : syracuseStep 2507357 = 940259) (by norm_num)
theorem B6341237 : Blo 1670035 6341237 := bbase (se 5 (by rfl) ⟨297245, by rfl⟩ : syracuseStep 6341237 = 594491) (by norm_num)
theorem B3760757 : Blo 1670035 3760757 := bbase (se 5 (by rfl) ⟨176285, by rfl⟩ : syracuseStep 3760757 = 352571) (by norm_num)
theorem B2507381 : Blo 1670035 2507381 := bbase (se 5 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 2507381 = 235067) (by norm_num)
theorem B2818685 : Blo 1670035 2818685 := bbase (se 3 (by rfl) ⟨528503, by rfl⟩ : syracuseStep 2818685 = 1057007) (by norm_num)
theorem B2507405 : Blo 1670035 2507405 := bbase (se 3 (by rfl) ⟨470138, by rfl⟩ : syracuseStep 2507405 = 940277) (by norm_num)
theorem B2114201 : Blo 1670035 2114201 := bbase (se 2 (by rfl) ⟨792825, by rfl⟩ : syracuseStep 2114201 = 1585651) (by norm_num)
theorem B2507429 : Blo 1670035 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B5636789 : Blo 1670035 5636789 := bbase (se 5 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 5636789 = 528449) (by norm_num)
theorem B3760829 : Blo 1670035 3760829 := bbase (se 3 (by rfl) ⟨705155, by rfl⟩ : syracuseStep 3760829 = 1410311) (by norm_num)
theorem B2507453 : Blo 1670035 2507453 := bbase (se 3 (by rfl) ⟨470147, by rfl⟩ : syracuseStep 2507453 = 940295) (by norm_num)
theorem B2114257 : Blo 1670035 2114257 := bbase (se 2 (by rfl) ⟨792846, by rfl⟩ : syracuseStep 2114257 = 1585693) (by norm_num)
theorem B2507477 : Blo 1670035 2507477 := bbase (se 7 (by rfl) ⟨29384, by rfl⟩ : syracuseStep 2507477 = 58769) (by norm_num)
theorem B2507501 : Blo 1670035 2507501 := bbase (se 3 (by rfl) ⟨470156, by rfl⟩ : syracuseStep 2507501 = 940313) (by norm_num)
theorem B2818813 : Blo 1670035 2818813 := bbase (se 3 (by rfl) ⟨528527, by rfl⟩ : syracuseStep 2818813 = 1057055) (by norm_num)
theorem B3760901 : Blo 1670035 3760901 := bbase (se 4 (by rfl) ⟨352584, by rfl⟩ : syracuseStep 3760901 = 705169) (by norm_num)
theorem B2507525 : Blo 1670035 2507525 := bbase (se 4 (by rfl) ⟨235080, by rfl⟩ : syracuseStep 2507525 = 470161) (by norm_num)
theorem B2507549 : Blo 1670035 2507549 := bbase (se 3 (by rfl) ⟨470165, by rfl⟩ : syracuseStep 2507549 = 940331) (by norm_num)
theorem B2114353 : Blo 1670035 2114353 := bbase (se 2 (by rfl) ⟨792882, by rfl⟩ : syracuseStep 2114353 = 1585765) (by norm_num)
theorem B2507573 : Blo 1670035 2507573 := bbase (se 5 (by rfl) ⟨117542, by rfl⟩ : syracuseStep 2507573 = 235085) (by norm_num)
theorem B6275893 : Blo 1670035 6275893 := bbase (se 5 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 6275893 = 588365) (by norm_num)
theorem B3760973 : Blo 1670035 3760973 := bbase (se 3 (by rfl) ⟨705182, by rfl⟩ : syracuseStep 3760973 = 1410365) (by norm_num)
theorem B2507597 : Blo 1670035 2507597 := bbase (se 3 (by rfl) ⟨470174, by rfl⟩ : syracuseStep 2507597 = 940349) (by norm_num)
theorem B2818901 : Blo 1670035 2818901 := bbase (se 9 (by rfl) ⟨8258, by rfl⟩ : syracuseStep 2818901 = 16517) (by norm_num)
theorem B2507621 : Blo 1670035 2507621 := bbase (se 4 (by rfl) ⟨235089, by rfl⟩ : syracuseStep 2507621 = 470179) (by norm_num)
theorem B2540413 : Blo 1670035 2540413 := bbase (se 3 (by rfl) ⟨476327, by rfl⟩ : syracuseStep 2540413 = 952655) (by norm_num)
theorem B2507645 : Blo 1670035 2507645 := bbase (se 3 (by rfl) ⟨470183, by rfl⟩ : syracuseStep 2507645 = 940367) (by norm_num)
theorem B3761045 : Blo 1670035 3761045 := bbase (se 6 (by rfl) ⟨88149, by rfl⟩ : syracuseStep 3761045 = 176299) (by norm_num)
theorem B2507669 : Blo 1670035 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B4227997 : Blo 1670035 4227997 := bbase (se 3 (by rfl) ⟨792749, by rfl⟩ : syracuseStep 4227997 = 1585499) (by norm_num)
theorem B2507693 : Blo 1670035 2507693 := bbase (se 3 (by rfl) ⟨470192, by rfl⟩ : syracuseStep 2507693 = 940385) (by norm_num)
theorem B2507717 : Blo 1670035 2507717 := bbase (se 4 (by rfl) ⟨235098, by rfl⟩ : syracuseStep 2507717 = 470197) (by norm_num)
theorem B2819029 : Blo 1670035 2819029 := bbase (se 7 (by rfl) ⟨33035, by rfl⟩ : syracuseStep 2819029 = 66071) (by norm_num)
theorem B2114525 : Blo 1670035 2114525 := bbase (se 3 (by rfl) ⟨396473, by rfl⟩ : syracuseStep 2114525 = 792947) (by norm_num)
theorem B3761117 : Blo 1670035 3761117 := bbase (se 3 (by rfl) ⟨705209, by rfl⟩ : syracuseStep 3761117 = 1410419) (by norm_num)
theorem B2507741 : Blo 1670035 2507741 := bbase (se 3 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 2507741 = 940403) (by norm_num)
theorem B2507765 : Blo 1670035 2507765 := bbase (se 5 (by rfl) ⟨117551, by rfl⟩ : syracuseStep 2507765 = 235103) (by norm_num)
theorem B3171325 : Blo 1670035 3171325 := bbase (se 3 (by rfl) ⟨594623, by rfl⟩ : syracuseStep 3171325 = 1189247) (by norm_num)
theorem B8463365 : Blo 1670035 8463365 := bbase (se 4 (by rfl) ⟨793440, by rfl⟩ : syracuseStep 8463365 = 1586881) (by norm_num)
theorem B4228109 : Blo 1670035 4228109 := bbase (se 3 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 4228109 = 1585541) (by norm_num)
theorem B2507789 : Blo 1670035 2507789 := bbase (se 3 (by rfl) ⟨470210, by rfl⟩ : syracuseStep 2507789 = 940421) (by norm_num)
theorem B10298389 : Blo 1670035 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B2114581 : Blo 1670035 2114581 := bbase (se 6 (by rfl) ⟨49560, by rfl⟩ : syracuseStep 2114581 = 99121) (by norm_num)
theorem B3761189 : Blo 1670035 3761189 := bbase (se 4 (by rfl) ⟨352611, by rfl⟩ : syracuseStep 3761189 = 705223) (by norm_num)
theorem B2507813 : Blo 1670035 2507813 := bbase (se 4 (by rfl) ⟨235107, by rfl⟩ : syracuseStep 2507813 = 470215) (by norm_num)
theorem B2819117 : Blo 1670035 2819117 := bbase (se 3 (by rfl) ⟨528584, by rfl⟩ : syracuseStep 2819117 = 1057169) (by norm_num)
theorem B2507837 : Blo 1670035 2507837 := bbase (se 3 (by rfl) ⟨470219, by rfl⟩ : syracuseStep 2507837 = 940439) (by norm_num)
theorem B2507861 : Blo 1670035 2507861 := bbase (se 8 (by rfl) ⟨14694, by rfl⟩ : syracuseStep 2507861 = 29389) (by norm_num)
theorem B5637221 : Blo 1670035 5637221 := bbase (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) (by norm_num)
theorem B3761261 : Blo 1670035 3761261 := bbase (se 3 (by rfl) ⟨705236, by rfl⟩ : syracuseStep 3761261 = 1410473) (by norm_num)
theorem B2507885 : Blo 1670035 2507885 := bbase (se 3 (by rfl) ⟨470228, by rfl⟩ : syracuseStep 2507885 = 940457) (by norm_num)
theorem B2114677 : Blo 1670035 2114677 := bbase (se 5 (by rfl) ⟨99125, by rfl⟩ : syracuseStep 2114677 = 198251) (by norm_num)
theorem B2507909 : Blo 1670035 2507909 := bbase (se 4 (by rfl) ⟨235116, by rfl⟩ : syracuseStep 2507909 = 470233) (by norm_num)
theorem B3171469 : Blo 1670035 3171469 := bbase (se 3 (by rfl) ⟨594650, by rfl⟩ : syracuseStep 3171469 = 1189301) (by norm_num)
theorem B2507933 : Blo 1670035 2507933 := bbase (se 3 (by rfl) ⟨470237, by rfl⟩ : syracuseStep 2507933 = 940475) (by norm_num)
theorem B2819245 : Blo 1670035 2819245 := bbase (se 3 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 2819245 = 1057217) (by norm_num)
theorem B3761333 : Blo 1670035 3761333 := bbase (se 5 (by rfl) ⟨176312, by rfl⟩ : syracuseStep 3761333 = 352625) (by norm_num)
theorem B2507957 : Blo 1670035 2507957 := bbase (se 5 (by rfl) ⟨117560, by rfl⟩ : syracuseStep 2507957 = 235121) (by norm_num)
theorem B2008253 : Blo 1670035 2008253 := bbase (se 3 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 2008253 = 753095) (by norm_num)
theorem B4228301 : Blo 1670035 4228301 := bbase (se 3 (by rfl) ⟨792806, by rfl⟩ : syracuseStep 4228301 = 1585613) (by norm_num)
theorem B2507981 : Blo 1670035 2507981 := bbase (se 3 (by rfl) ⟨470246, by rfl⟩ : syracuseStep 2507981 = 940493) (by norm_num)
theorem B3433693 : Blo 1670035 3433693 := bbase (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) (by norm_num)
theorem B4015325 : Blo 1670035 4015325 := bbase (se 3 (by rfl) ⟨752873, by rfl⟩ : syracuseStep 4015325 = 1505747) (by norm_num)
theorem B2508005 : Blo 1670035 2508005 := bbase (se 4 (by rfl) ⟨235125, by rfl⟩ : syracuseStep 2508005 = 470251) (by norm_num)
theorem B3761405 : Blo 1670035 3761405 := bbase (se 3 (by rfl) ⟨705263, by rfl⟩ : syracuseStep 3761405 = 1410527) (by norm_num)
theorem B2508029 : Blo 1670035 2508029 := bbase (se 3 (by rfl) ⟨470255, by rfl⟩ : syracuseStep 2508029 = 940511) (by norm_num)
theorem B2819333 : Blo 1670035 2819333 := bbase (se 4 (by rfl) ⟨264312, by rfl⟩ : syracuseStep 2819333 = 528625) (by norm_num)
theorem B2508053 : Blo 1670035 2508053 := bbase (se 6 (by rfl) ⟨58782, by rfl⟩ : syracuseStep 2508053 = 117565) (by norm_num)
theorem B2114849 : Blo 1670035 2114849 := bbase (se 2 (by rfl) ⟨793068, by rfl⟩ : syracuseStep 2114849 = 1586137) (by norm_num)
theorem B3171629 : Blo 1670035 3171629 := bbase (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) (by norm_num)
theorem B3761477 : Blo 1670035 3761477 := bbase (se 4 (by rfl) ⟨352638, by rfl⟩ : syracuseStep 3761477 = 705277) (by norm_num)
theorem B2114905 : Blo 1670035 2114905 := bbase (se 2 (by rfl) ⟨793089, by rfl⟩ : syracuseStep 2114905 = 1586179) (by norm_num)
theorem B2819461 : Blo 1670035 2819461 := bbase (se 4 (by rfl) ⟨264324, by rfl⟩ : syracuseStep 2819461 = 528649) (by norm_num)
theorem B3761549 : Blo 1670035 3761549 := bbase (se 3 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 3761549 = 1410581) (by norm_num)
theorem B8455589 : Blo 1670035 8455589 := bbase (se 4 (by rfl) ⟨792711, by rfl⟩ : syracuseStep 8455589 = 1585423) (by norm_num)
theorem B2115001 : Blo 1670035 2115001 := bbase (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) (by norm_num)
theorem B3171773 : Blo 1670035 3171773 := bbase (se 3 (by rfl) ⟨594707, by rfl⟩ : syracuseStep 3171773 = 1189415) (by norm_num)
theorem B3761621 : Blo 1670035 3761621 := bbase (se 7 (by rfl) ⟨44081, by rfl⟩ : syracuseStep 3761621 = 88163) (by norm_num)
theorem B2819549 : Blo 1670035 2819549 := bbase (se 3 (by rfl) ⟨528665, by rfl⟩ : syracuseStep 2819549 = 1057331) (by norm_num)
theorem B11429365 : Blo 1670035 11429365 := bbase (se 5 (by rfl) ⟨535751, by rfl⟩ : syracuseStep 11429365 = 1071503) (by norm_num)
theorem B7620085 : Blo 1670035 7620085 := bbase (se 5 (by rfl) ⟨357191, by rfl⟩ : syracuseStep 7620085 = 714383) (by norm_num)
theorem B2008585 : Blo 1670035 2008585 := bbase (se 2 (by rfl) ⟨753219, by rfl⟩ : syracuseStep 2008585 = 1506439) (by norm_num)
theorem B5637653 : Blo 1670035 5637653 := bbase (se 6 (by rfl) ⟨132132, by rfl⟩ : syracuseStep 5637653 = 264265) (by norm_num)
theorem B3761693 : Blo 1670035 3761693 := bbase (se 3 (by rfl) ⟨705317, by rfl⟩ : syracuseStep 3761693 = 1410635) (by norm_num)
theorem B4228645 : Blo 1670035 4228645 := bbase (se 4 (by rfl) ⟨396435, by rfl⟩ : syracuseStep 4228645 = 792871) (by norm_num)
theorem B15238709 : Blo 1670035 15238709 := bbase (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) (by norm_num)
theorem B10298933 : Blo 1670035 10298933 := bbase (se 5 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 10298933 = 965525) (by norm_num)
theorem B5350997 : Blo 1670035 5350997 := bbase (se 8 (by rfl) ⟨31353, by rfl⟩ : syracuseStep 5350997 = 62707) (by norm_num)
theorem B2819677 : Blo 1670035 2819677 := bbase (se 3 (by rfl) ⟨528689, by rfl⟩ : syracuseStep 2819677 = 1057379) (by norm_num)
theorem B4015709 : Blo 1670035 4015709 := bbase (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) (by norm_num)
theorem B2115173 : Blo 1670035 2115173 := bbase (se 4 (by rfl) ⟨198297, by rfl⟩ : syracuseStep 2115173 = 396595) (by norm_num)
theorem B3761765 : Blo 1670035 3761765 := bbase (se 4 (by rfl) ⟨352665, by rfl⟩ : syracuseStep 3761765 = 705331) (by norm_num)
theorem B11437685 : Blo 1670035 11437685 := bbase (se 5 (by rfl) ⟨536141, by rfl⟩ : syracuseStep 11437685 = 1072283) (by norm_num)
theorem B4228757 : Blo 1670035 4228757 := bbase (se 6 (by rfl) ⟨99111, by rfl⟩ : syracuseStep 4228757 = 198223) (by norm_num)
theorem B2115229 : Blo 1670035 2115229 := bbase (se 3 (by rfl) ⟨396605, by rfl⟩ : syracuseStep 2115229 = 793211) (by norm_num)
theorem B3761837 : Blo 1670035 3761837 := bbase (se 3 (by rfl) ⟨705344, by rfl⟩ : syracuseStep 3761837 = 1410689) (by norm_num)
theorem B2819765 : Blo 1670035 2819765 := bbase (se 5 (by rfl) ⟨132176, by rfl⟩ : syracuseStep 2819765 = 264353) (by norm_num)
theorem B24094421 : Blo 1670035 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B3172061 : Blo 1670035 3172061 := bbase (se 3 (by rfl) ⟨594761, by rfl⟩ : syracuseStep 3172061 = 1189523) (by norm_num)
theorem B3761909 : Blo 1670035 3761909 := bbase (se 5 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 3761909 = 352679) (by norm_num)
theorem B2115325 : Blo 1670035 2115325 := bbase (se 3 (by rfl) ⟨396623, by rfl⟩ : syracuseStep 2115325 = 793247) (by norm_num)
theorem B6342421 : Blo 1670035 6342421 := bbase (se 6 (by rfl) ⟨148650, by rfl⟩ : syracuseStep 6342421 = 297301) (by norm_num)
theorem B19040021 : Blo 1670035 19040021 := bbase (se 6 (by rfl) ⟨446250, by rfl⟩ : syracuseStep 19040021 = 892501) (by norm_num)
theorem B4015909 : Blo 1670035 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B2819893 : Blo 1670035 2819893 := bbase (se 5 (by rfl) ⟨132182, by rfl⟩ : syracuseStep 2819893 = 264365) (by norm_num)
theorem B3434293 : Blo 1670035 3434293 := bbase (se 5 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 3434293 = 321965) (by norm_num)
theorem B3761981 : Blo 1670035 3761981 := bbase (se 3 (by rfl) ⟨705371, by rfl⟩ : syracuseStep 3761981 = 1410743) (by norm_num)
theorem B4228949 : Blo 1670035 4228949 := bbase (se 9 (by rfl) ⟨12389, by rfl⟩ : syracuseStep 4228949 = 24779) (by norm_num)
theorem B3172213 : Blo 1670035 3172213 := bbase (se 5 (by rfl) ⟨148697, by rfl⟩ : syracuseStep 3172213 = 297395) (by norm_num)
theorem B3762053 : Blo 1670035 3762053 := bbase (se 4 (by rfl) ⟨352692, by rfl⟩ : syracuseStep 3762053 = 705385) (by norm_num)
theorem B2819981 : Blo 1670035 2819981 := bbase (se 3 (by rfl) ⟨528746, by rfl⟩ : syracuseStep 2819981 = 1057493) (by norm_num)
theorem B7137173 : Blo 1670035 7137173 := bbase (se 6 (by rfl) ⟨167277, by rfl⟩ : syracuseStep 7137173 = 334555) (by norm_num)
theorem B2115497 : Blo 1670035 2115497 := bbase (se 2 (by rfl) ⟨793311, by rfl⟩ : syracuseStep 2115497 = 1586623) (by norm_num)
theorem B5638085 : Blo 1670035 5638085 := bbase (se 4 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 5638085 = 1057141) (by norm_num)
theorem B2115553 : Blo 1670035 2115553 := bbase (se 2 (by rfl) ⟨793332, by rfl⟩ : syracuseStep 2115553 = 1586665) (by norm_num)
theorem B6023173 : Blo 1670035 6023173 := bbase (se 4 (by rfl) ⟨564672, by rfl⟩ : syracuseStep 6023173 = 1129345) (by norm_num)
theorem B2820109 : Blo 1670035 2820109 := bbase (se 3 (by rfl) ⟨528770, by rfl⟩ : syracuseStep 2820109 = 1057541) (by norm_num)
theorem B2115649 : Blo 1670035 2115649 := bbase (se 2 (by rfl) ⟨793368, by rfl⟩ : syracuseStep 2115649 = 1586737) (by norm_num)
theorem B6342725 : Blo 1670035 6342725 := bbase (se 4 (by rfl) ⟨594630, by rfl⟩ : syracuseStep 6342725 = 1189261) (by norm_num)
theorem B2820197 : Blo 1670035 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B7940213 : Blo 1670035 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B8030357 : Blo 1670035 8030357 := bbase (se 6 (by rfl) ⟨188211, by rfl⟩ : syracuseStep 8030357 = 376423) (by norm_num)
theorem B3172517 : Blo 1670035 3172517 := bbase (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) (by norm_num)
theorem B4229293 : Blo 1670035 4229293 := bbase (se 3 (by rfl) ⟨792992, by rfl⟩ : syracuseStep 4229293 = 1585985) (by norm_num)
theorem B9521333 : Blo 1670035 9521333 := bbase (se 5 (by rfl) ⟨446312, by rfl⟩ : syracuseStep 9521333 = 892625) (by norm_num)
theorem B2820325 : Blo 1670035 2820325 := bbase (se 4 (by rfl) ⟨264405, by rfl⟩ : syracuseStep 2820325 = 528811) (by norm_num)
theorem B2115821 : Blo 1670035 2115821 := bbase (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) (by norm_num)
theorem B17148149 : Blo 1670035 17148149 := bbase (se 5 (by rfl) ⟨803819, by rfl⟩ : syracuseStep 17148149 = 1607639) (by norm_num)
theorem B8464661 : Blo 1670035 8464661 := bbase (se 6 (by rfl) ⟨198390, by rfl⟩ : syracuseStep 8464661 = 396781) (by norm_num)
theorem B4229405 : Blo 1670035 4229405 := bbase (se 3 (by rfl) ⟨793013, by rfl⟩ : syracuseStep 4229405 = 1586027) (by norm_num)
theorem B2115877 : Blo 1670035 2115877 := bbase (se 4 (by rfl) ⟨198363, by rfl⟩ : syracuseStep 2115877 = 396727) (by norm_num)
theorem B2820413 : Blo 1670035 2820413 := bbase (se 3 (by rfl) ⟨528827, by rfl⟩ : syracuseStep 2820413 = 1057655) (by norm_num)
theorem B10701173 : Blo 1670035 10701173 := bbase (se 5 (by rfl) ⟨501617, by rfl⟩ : syracuseStep 10701173 = 1003235) (by norm_num)
theorem B2378101 : Blo 1670035 2378101 := bbase (se 5 (by rfl) ⟨111473, by rfl⟩ : syracuseStep 2378101 = 222947) (by norm_num)
theorem B5638517 : Blo 1670035 5638517 := bbase (se 5 (by rfl) ⟨264305, by rfl⟩ : syracuseStep 5638517 = 528611) (by norm_num)
theorem B2115973 : Blo 1670035 2115973 := bbase (se 4 (by rfl) ⟨198372, by rfl⟩ : syracuseStep 2115973 = 396745) (by norm_num)
theorem B2820541 : Blo 1670035 2820541 := bbase (se 3 (by rfl) ⟨528851, by rfl⟩ : syracuseStep 2820541 = 1057703) (by norm_num)
theorem B36628949 : Blo 1670035 36628949 := bbase (se 7 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 36628949 = 858491) (by norm_num)
theorem B4229597 : Blo 1670035 4229597 := bbase (se 3 (by rfl) ⟨793049, by rfl⟩ : syracuseStep 4229597 = 1586099) (by norm_num)
theorem B2542085 : Blo 1670035 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B2820629 : Blo 1670035 2820629 := bbase (se 6 (by rfl) ⟨66108, by rfl⟩ : syracuseStep 2820629 = 132217) (by norm_num)
theorem B2116145 : Blo 1670035 2116145 := bbase (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) (by norm_num)
theorem B2378317 : Blo 1670035 2378317 := bbase (se 3 (by rfl) ⟨445934, by rfl⟩ : syracuseStep 2378317 = 891869) (by norm_num)
theorem B5352085 : Blo 1670035 5352085 := bbase (se 6 (by rfl) ⟨125439, by rfl⟩ : syracuseStep 5352085 = 250879) (by norm_num)
theorem B2820757 : Blo 1670035 2820757 := bbase (se 6 (by rfl) ⟨66111, by rfl⟩ : syracuseStep 2820757 = 132223) (by norm_num)
theorem B1739441 : Blo 1670035 1739441 := bbase (se 2 (by rfl) ⟨652290, by rfl⟩ : syracuseStep 1739441 = 1304581) (by norm_num)
theorem B8456885 : Blo 1670035 8456885 := bbase (se 5 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 8456885 = 792833) (by norm_num)
theorem B6023909 : Blo 1670035 6023909 := bbase (se 4 (by rfl) ⟨564741, by rfl⟩ : syracuseStep 6023909 = 1129483) (by norm_num)
theorem B2820845 : Blo 1670035 2820845 := bbase (se 3 (by rfl) ⟨528908, by rfl⟩ : syracuseStep 2820845 = 1057817) (by norm_num)
theorem B1878817 : Blo 1670035 1878817 := bbase (se 2 (by rfl) ⟨704556, by rfl⟩ : syracuseStep 1878817 = 1409113) (by norm_num)
theorem B5638949 : Blo 1670035 5638949 := bbase (se 4 (by rfl) ⟨528651, by rfl⟩ : syracuseStep 5638949 = 1057303) (by norm_num)
theorem B4229941 : Blo 1670035 4229941 := bbase (se 5 (by rfl) ⟨198278, by rfl⟩ : syracuseStep 4229941 = 396557) (by norm_num)
theorem B1878853 : Blo 1670035 1878853 := bbase (se 4 (by rfl) ⟨176142, by rfl⟩ : syracuseStep 1878853 = 352285) (by norm_num)
theorem B1878889 : Blo 1670035 1878889 := bbase (se 2 (by rfl) ⟨704583, by rfl⟩ : syracuseStep 1878889 = 1409167) (by norm_num)
theorem B2820973 : Blo 1670035 2820973 := bbase (se 3 (by rfl) ⟨528932, by rfl⟩ : syracuseStep 2820973 = 1057865) (by norm_num)
theorem B8031109 : Blo 1670035 8031109 := bbase (se 4 (by rfl) ⟨752916, by rfl⟩ : syracuseStep 8031109 = 1505833) (by norm_num)
theorem B1878925 : Blo 1670035 1878925 := bbase (se 3 (by rfl) ⟨352298, by rfl⟩ : syracuseStep 1878925 = 704597) (by norm_num)
theorem B3173269 : Blo 1670035 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B4230053 : Blo 1670035 4230053 := bbase (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) (by norm_num)
theorem B1878961 : Blo 1670035 1878961 := bbase (se 2 (by rfl) ⟨704610, by rfl⟩ : syracuseStep 1878961 = 1409221) (by norm_num)
theorem B12864437 : Blo 1670035 12864437 := bbase (se 5 (by rfl) ⟨603020, by rfl⟩ : syracuseStep 12864437 = 1206041) (by norm_num)
theorem B2378693 : Blo 1670035 2378693 := bbase (se 4 (by rfl) ⟨223002, by rfl⟩ : syracuseStep 2378693 = 446005) (by norm_num)
theorem B2821061 : Blo 1670035 2821061 := bbase (se 4 (by rfl) ⟨264474, by rfl⟩ : syracuseStep 2821061 = 528949) (by norm_num)
theorem B1878997 : Blo 1670035 1878997 := bbase (se 7 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 1878997 = 44039) (by norm_num)
theorem B1879033 : Blo 1670035 1879033 := bbase (se 2 (by rfl) ⟨704637, by rfl⟩ : syracuseStep 1879033 = 1409275) (by norm_num)
theorem B1879069 : Blo 1670035 1879069 := bbase (se 3 (by rfl) ⟨352325, by rfl⟩ : syracuseStep 1879069 = 704651) (by norm_num)
theorem B3173413 : Blo 1670035 3173413 := bbase (se 4 (by rfl) ⟨297507, by rfl⟩ : syracuseStep 3173413 = 595015) (by norm_num)
theorem B1879105 : Blo 1670035 1879105 := bbase (se 2 (by rfl) ⟨704664, by rfl⟩ : syracuseStep 1879105 = 1409329) (by norm_num)
theorem B2821189 : Blo 1670035 2821189 := bbase (se 4 (by rfl) ⟨264486, by rfl⟩ : syracuseStep 2821189 = 528973) (by norm_num)
theorem B1879141 : Blo 1670035 1879141 := bbase (se 4 (by rfl) ⟨176169, by rfl⟩ : syracuseStep 1879141 = 352339) (by norm_num)
theorem B4230245 : Blo 1670035 4230245 := bbase (se 4 (by rfl) ⟨396585, by rfl⟩ : syracuseStep 4230245 = 793171) (by norm_num)
theorem B1879177 : Blo 1670035 1879177 := bbase (se 2 (by rfl) ⟨704691, by rfl⟩ : syracuseStep 1879177 = 1409383) (by norm_num)
theorem B2821277 : Blo 1670035 2821277 := bbase (se 3 (by rfl) ⟨528989, by rfl⟩ : syracuseStep 2821277 = 1057979) (by norm_num)
theorem B1879213 : Blo 1670035 1879213 := bbase (se 3 (by rfl) ⟨352352, by rfl⟩ : syracuseStep 1879213 = 704705) (by norm_num)
theorem B3173573 : Blo 1670035 3173573 := bbase (se 4 (by rfl) ⟨297522, by rfl⟩ : syracuseStep 3173573 = 595045) (by norm_num)
theorem B3214541 : Blo 1670035 3214541 := bbase (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) (by norm_num)
theorem B1879249 : Blo 1670035 1879249 := bbase (se 2 (by rfl) ⟨704718, by rfl⟩ : syracuseStep 1879249 = 1409437) (by norm_num)
theorem B5639381 : Blo 1670035 5639381 := bbase (se 7 (by rfl) ⟨66086, by rfl⟩ : syracuseStep 5639381 = 132173) (by norm_num)
theorem B1879285 : Blo 1670035 1879285 := bbase (se 5 (by rfl) ⟨88091, by rfl⟩ : syracuseStep 1879285 = 176183) (by norm_num)
theorem B3812597 : Blo 1670035 3812597 := bbase (se 5 (by rfl) ⟨178715, by rfl⟩ : syracuseStep 3812597 = 357431) (by norm_num)
theorem B4640021 : Blo 1670035 4640021 := bbase (se 6 (by rfl) ⟨108750, by rfl⟩ : syracuseStep 4640021 = 217501) (by norm_num)
theorem B1879321 : Blo 1670035 1879321 := bbase (se 2 (by rfl) ⟨704745, by rfl⟩ : syracuseStep 1879321 = 1409491) (by norm_num)
theorem B2821405 : Blo 1670035 2821405 := bbase (se 3 (by rfl) ⟨529013, by rfl⟩ : syracuseStep 2821405 = 1058027) (by norm_num)
theorem B1879357 : Blo 1670035 1879357 := bbase (se 3 (by rfl) ⟨352379, by rfl⟩ : syracuseStep 1879357 = 704759) (by norm_num)
theorem B3173717 : Blo 1670035 3173717 := bbase (se 11 (by rfl) ⟨2324, by rfl⟩ : syracuseStep 3173717 = 4649) (by norm_num)
theorem B1879393 : Blo 1670035 1879393 := bbase (se 2 (by rfl) ⟨704772, by rfl⟩ : syracuseStep 1879393 = 1409545) (by norm_num)
theorem B2821493 : Blo 1670035 2821493 := bbase (se 5 (by rfl) ⟨132257, by rfl⟩ : syracuseStep 2821493 = 264515) (by norm_num)
theorem B1879429 : Blo 1670035 1879429 := bbase (se 4 (by rfl) ⟨176196, by rfl⟩ : syracuseStep 1879429 = 352393) (by norm_num)
theorem B13553045 : Blo 1670035 13553045 := bbase (se 6 (by rfl) ⟨317649, by rfl⟩ : syracuseStep 13553045 = 635299) (by norm_num)
theorem B6024613 : Blo 1670035 6024613 := bbase (se 4 (by rfl) ⟨564807, by rfl⟩ : syracuseStep 6024613 = 1129615) (by norm_num)
theorem B1879465 : Blo 1670035 1879465 := bbase (se 2 (by rfl) ⟨704799, by rfl⟩ : syracuseStep 1879465 = 1409599) (by norm_num)
theorem B4230589 : Blo 1670035 4230589 := bbase (se 3 (by rfl) ⟨793235, by rfl⟩ : syracuseStep 4230589 = 1586471) (by norm_num)
theorem B1879501 : Blo 1670035 1879501 := bbase (se 3 (by rfl) ⟨352406, by rfl⟩ : syracuseStep 1879501 = 704813) (by norm_num)
theorem B1879537 : Blo 1670035 1879537 := bbase (se 2 (by rfl) ⟨704826, by rfl⟩ : syracuseStep 1879537 = 1409653) (by norm_num)
theorem B1879573 : Blo 1670035 1879573 := bbase (se 6 (by rfl) ⟨44052, by rfl⟩ : syracuseStep 1879573 = 88105) (by norm_num)
theorem B7622165 : Blo 1670035 7622165 := bbase (se 6 (by rfl) ⟨178644, by rfl⟩ : syracuseStep 7622165 = 357289) (by norm_num)
theorem B4230701 : Blo 1670035 4230701 := bbase (se 3 (by rfl) ⟨793256, by rfl⟩ : syracuseStep 4230701 = 1586513) (by norm_num)
theorem B1879609 : Blo 1670035 1879609 := bbase (se 2 (by rfl) ⟨704853, by rfl⟩ : syracuseStep 1879609 = 1409707) (by norm_num)
theorem B1879645 : Blo 1670035 1879645 := bbase (se 3 (by rfl) ⟨352433, by rfl⟩ : syracuseStep 1879645 = 704867) (by norm_num)
theorem B3174005 : Blo 1670035 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B1879681 : Blo 1670035 1879681 := bbase (se 2 (by rfl) ⟨704880, by rfl⟩ : syracuseStep 1879681 = 1409761) (by norm_num)
theorem B5639813 : Blo 1670035 5639813 := bbase (se 4 (by rfl) ⟨528732, by rfl⟩ : syracuseStep 5639813 = 1057465) (by norm_num)
theorem B1879717 : Blo 1670035 1879717 := bbase (se 4 (by rfl) ⟨176223, by rfl⟩ : syracuseStep 1879717 = 352447) (by norm_num)
theorem B1879753 : Blo 1670035 1879753 := bbase (se 2 (by rfl) ⟨704907, by rfl⟩ : syracuseStep 1879753 = 1409815) (by norm_num)
theorem B1879789 : Blo 1670035 1879789 := bbase (se 3 (by rfl) ⟨352460, by rfl⟩ : syracuseStep 1879789 = 704921) (by norm_num)
theorem B4230893 : Blo 1670035 4230893 := bbase (se 3 (by rfl) ⟨793292, by rfl⟩ : syracuseStep 4230893 = 1586585) (by norm_num)
theorem B3174157 : Blo 1670035 3174157 := bbase (se 3 (by rfl) ⟨595154, by rfl⟩ : syracuseStep 3174157 = 1190309) (by norm_num)
theorem B1879825 : Blo 1670035 1879825 := bbase (se 2 (by rfl) ⟨704934, by rfl⟩ : syracuseStep 1879825 = 1409869) (by norm_num)
theorem B5353253 : Blo 1670035 5353253 := bbase (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) (by norm_num)
theorem B1879861 : Blo 1670035 1879861 := bbase (se 5 (by rfl) ⟨88118, by rfl⟩ : syracuseStep 1879861 = 176237) (by norm_num)
theorem B1879897 : Blo 1670035 1879897 := bbase (se 2 (by rfl) ⟨704961, by rfl⟩ : syracuseStep 1879897 = 1409923) (by norm_num)
theorem B1879933 : Blo 1670035 1879933 := bbase (se 3 (by rfl) ⟨352487, by rfl⟩ : syracuseStep 1879933 = 704975) (by norm_num)
theorem B3567493 : Blo 1670035 3567493 := bbase (se 4 (by rfl) ⟨334452, by rfl⟩ : syracuseStep 3567493 = 668905) (by norm_num)
theorem B12046229 : Blo 1670035 12046229 := bbase (se 6 (by rfl) ⟨282333, by rfl⟩ : syracuseStep 12046229 = 564667) (by norm_num)
theorem B1879969 : Blo 1670035 1879969 := bbase (se 2 (by rfl) ⟨704988, by rfl⟩ : syracuseStep 1879969 = 1409977) (by norm_num)
theorem B8458181 : Blo 1670035 8458181 := bbase (se 4 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 8458181 = 1585909) (by norm_num)
theorem B1880005 : Blo 1670035 1880005 := bbase (se 4 (by rfl) ⟨176250, by rfl⟩ : syracuseStep 1880005 = 352501) (by norm_num)
theorem B1880041 : Blo 1670035 1880041 := bbase (se 2 (by rfl) ⟨705015, by rfl⟩ : syracuseStep 1880041 = 1410031) (by norm_num)
theorem B1880077 : Blo 1670035 1880077 := bbase (se 3 (by rfl) ⟨352514, by rfl⟩ : syracuseStep 1880077 = 705029) (by norm_num)
theorem B3387413 : Blo 1670035 3387413 := bbase (se 6 (by rfl) ⟨79392, by rfl⟩ : syracuseStep 3387413 = 158785) (by norm_num)
theorem B1880113 : Blo 1670035 1880113 := bbase (se 2 (by rfl) ⟨705042, by rfl⟩ : syracuseStep 1880113 = 1410085) (by norm_num)
theorem B1904693 : Blo 1670035 1904693 := bbase (se 5 (by rfl) ⟨89282, by rfl⟩ : syracuseStep 1904693 = 178565) (by norm_num)
theorem B5640245 : Blo 1670035 5640245 := bbase (se 5 (by rfl) ⟨264386, by rfl⟩ : syracuseStep 5640245 = 528773) (by norm_num)
theorem B4231237 : Blo 1670035 4231237 := bbase (se 4 (by rfl) ⟨396678, by rfl⟩ : syracuseStep 4231237 = 793357) (by norm_num)
theorem B1880149 : Blo 1670035 1880149 := bbase (se 8 (by rfl) ⟨11016, by rfl⟩ : syracuseStep 1880149 = 22033) (by norm_num)
theorem B1880185 : Blo 1670035 1880185 := bbase (se 2 (by rfl) ⟨705069, by rfl⟩ : syracuseStep 1880185 = 1410139) (by norm_num)
theorem B6344837 : Blo 1670035 6344837 := bbase (se 4 (by rfl) ⟨594828, by rfl⟩ : syracuseStep 6344837 = 1189657) (by norm_num)
theorem B1880221 : Blo 1670035 1880221 := bbase (se 3 (by rfl) ⟨352541, by rfl⟩ : syracuseStep 1880221 = 705083) (by norm_num)
theorem B4231349 : Blo 1670035 4231349 := bbase (se 5 (by rfl) ⟨198344, by rfl⟩ : syracuseStep 4231349 = 396689) (by norm_num)
theorem B1880257 : Blo 1670035 1880257 := bbase (se 2 (by rfl) ⟨705096, by rfl⟩ : syracuseStep 1880257 = 1410193) (by norm_num)
theorem B3010765 : Blo 1670035 3010765 := bbase (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) (by norm_num)
theorem B1880293 : Blo 1670035 1880293 := bbase (se 4 (by rfl) ⟨176277, by rfl⟩ : syracuseStep 1880293 = 352555) (by norm_num)
theorem B1880329 : Blo 1670035 1880329 := bbase (se 2 (by rfl) ⟨705123, by rfl⟩ : syracuseStep 1880329 = 1410247) (by norm_num)
theorem B1880365 : Blo 1670035 1880365 := bbase (se 3 (by rfl) ⟨352568, by rfl⟩ : syracuseStep 1880365 = 705137) (by norm_num)
theorem B1880401 : Blo 1670035 1880401 := bbase (se 2 (by rfl) ⟨705150, by rfl⟩ : syracuseStep 1880401 = 1410301) (by norm_num)
theorem B2257237 : Blo 1670035 2257237 := bbase (se 10 (by rfl) ⟨3306, by rfl⟩ : syracuseStep 2257237 = 6613) (by norm_num)
theorem B2380117 : Blo 1670035 2380117 := bbase (se 10 (by rfl) ⟨3486, by rfl⟩ : syracuseStep 2380117 = 6973) (by norm_num)
theorem B3567989 : Blo 1670035 3567989 := bbase (se 5 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 3567989 = 334499) (by norm_num)
theorem B1880437 : Blo 1670035 1880437 := bbase (se 5 (by rfl) ⟨88145, by rfl⟩ : syracuseStep 1880437 = 176291) (by norm_num)
theorem B4231541 : Blo 1670035 4231541 := bbase (se 5 (by rfl) ⟨198353, by rfl⟩ : syracuseStep 4231541 = 396707) (by norm_num)
theorem B1880473 : Blo 1670035 1880473 := bbase (se 2 (by rfl) ⟨705177, by rfl⟩ : syracuseStep 1880473 = 1410355) (by norm_num)
theorem B6345125 : Blo 1670035 6345125 := bbase (se 4 (by rfl) ⟨594855, by rfl⟩ : syracuseStep 6345125 = 1189711) (by norm_num)
theorem B1880509 : Blo 1670035 1880509 := bbase (se 3 (by rfl) ⟨352595, by rfl⟩ : syracuseStep 1880509 = 705191) (by norm_num)
theorem B1880545 : Blo 1670035 1880545 := bbase (se 2 (by rfl) ⟨705204, by rfl⟩ : syracuseStep 1880545 = 1410409) (by norm_num)
theorem B5640677 : Blo 1670035 5640677 := bbase (se 4 (by rfl) ⟨528813, by rfl⟩ : syracuseStep 5640677 = 1057627) (by norm_num)
theorem B2675197 : Blo 1670035 2675197 := bbase (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) (by norm_num)
theorem B1880581 : Blo 1670035 1880581 := bbase (se 4 (by rfl) ⟨176304, by rfl⟩ : syracuseStep 1880581 = 352609) (by norm_num)
theorem B3215893 : Blo 1670035 3215893 := bbase (se 6 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 3215893 = 150745) (by norm_num)
theorem B2142749 : Blo 1670035 2142749 := bbase (se 3 (by rfl) ⟨401765, by rfl⟩ : syracuseStep 2142749 = 803531) (by norm_num)
theorem B1880617 : Blo 1670035 1880617 := bbase (se 2 (by rfl) ⟨705231, by rfl⟩ : syracuseStep 1880617 = 1410463) (by norm_num)
theorem B1880653 : Blo 1670035 1880653 := bbase (se 3 (by rfl) ⟨352622, by rfl⟩ : syracuseStep 1880653 = 705245) (by norm_num)
theorem B2142821 : Blo 1670035 2142821 := bbase (se 4 (by rfl) ⟨200889, by rfl⟩ : syracuseStep 2142821 = 401779) (by norm_num)
theorem B1880689 : Blo 1670035 1880689 := bbase (se 2 (by rfl) ⟨705258, by rfl⟩ : syracuseStep 1880689 = 1410517) (by norm_num)
theorem B1905277 : Blo 1670035 1905277 := bbase (se 3 (by rfl) ⟨357239, by rfl⟩ : syracuseStep 1905277 = 714479) (by norm_num)
theorem B1880725 : Blo 1670035 1880725 := bbase (se 6 (by rfl) ⟨44079, by rfl⟩ : syracuseStep 1880725 = 88159) (by norm_num)
theorem B2257565 : Blo 1670035 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B4756133 : Blo 1670035 4756133 := bbase (se 4 (by rfl) ⟨445887, by rfl⟩ : syracuseStep 4756133 = 891775) (by norm_num)
theorem B3388085 : Blo 1670035 3388085 := bbase (se 5 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 3388085 = 317633) (by norm_num)
theorem B1880761 : Blo 1670035 1880761 := bbase (se 2 (by rfl) ⟨705285, by rfl⟩ : syracuseStep 1880761 = 1410571) (by norm_num)
theorem B3011269 : Blo 1670035 3011269 := bbase (se 4 (by rfl) ⟨282306, by rfl⟩ : syracuseStep 3011269 = 564613) (by norm_num)
theorem B4231885 : Blo 1670035 4231885 := bbase (se 3 (by rfl) ⟨793478, by rfl⟩ : syracuseStep 4231885 = 1586957) (by norm_num)
theorem B1880797 : Blo 1670035 1880797 := bbase (se 3 (by rfl) ⟨352649, by rfl⟩ : syracuseStep 1880797 = 705299) (by norm_num)
theorem B1880833 : Blo 1670035 1880833 := bbase (se 2 (by rfl) ⟨705312, by rfl⟩ : syracuseStep 1880833 = 1410625) (by norm_num)
theorem B1880869 : Blo 1670035 1880869 := bbase (se 4 (by rfl) ⟨176331, by rfl⟩ : syracuseStep 1880869 = 352663) (by norm_num)
theorem B4231997 : Blo 1670035 4231997 := bbase (se 3 (by rfl) ⟨793499, by rfl⟩ : syracuseStep 4231997 = 1586999) (by norm_num)
theorem B1880905 : Blo 1670035 1880905 := bbase (se 2 (by rfl) ⟨705339, by rfl⟩ : syracuseStep 1880905 = 1410679) (by norm_num)
theorem B1880941 : Blo 1670035 1880941 := bbase (se 3 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 1880941 = 705353) (by norm_num)
theorem B1880977 : Blo 1670035 1880977 := bbase (se 2 (by rfl) ⟨705366, by rfl⟩ : syracuseStep 1880977 = 1410733) (by norm_num)
theorem B5641109 : Blo 1670035 5641109 := bbase (se 6 (by rfl) ⟨132213, by rfl⟩ : syracuseStep 5641109 = 264427) (by norm_num)
theorem B1881013 : Blo 1670035 1881013 := bbase (se 5 (by rfl) ⟨88172, by rfl⟩ : syracuseStep 1881013 = 176345) (by norm_num)
theorem B4232189 : Blo 1670035 4232189 := bbase (se 3 (by rfl) ⟨793535, by rfl⟩ : syracuseStep 4232189 = 1587071) (by norm_num)
theorem B2675909 : Blo 1670035 2675909 := bbase (se 4 (by rfl) ⟨250866, by rfl⟩ : syracuseStep 2675909 = 501733) (by norm_num)
theorem B8459477 : Blo 1670035 8459477 := bbase (se 7 (by rfl) ⟨99134, by rfl⟩ : syracuseStep 8459477 = 198269) (by norm_num)
theorem B2258149 : Blo 1670035 2258149 := bbase (se 4 (by rfl) ⟨211701, by rfl⟩ : syracuseStep 2258149 = 423403) (by norm_num)
theorem B3568877 : Blo 1670035 3568877 := bbase (se 3 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 3568877 = 1338329) (by norm_num)
theorem B12694805 : Blo 1670035 12694805 := bbase (se 6 (by rfl) ⟨297534, by rfl⟩ : syracuseStep 12694805 = 595069) (by norm_num)
theorem B5641541 : Blo 1670035 5641541 := bbase (se 4 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 5641541 = 1057789) (by norm_num)
theorem B3568997 : Blo 1670035 3568997 := bbase (se 4 (by rfl) ⟨334593, by rfl⟩ : syracuseStep 3568997 = 669187) (by norm_num)
theorem B3757589 : Blo 1670035 3757589 := bbase (se 6 (by rfl) ⟨88068, by rfl⟩ : syracuseStep 3757589 = 176137) (by norm_num)
theorem B3012149 : Blo 1670035 3012149 := bbase (se 5 (by rfl) ⟨141194, by rfl⟩ : syracuseStep 3012149 = 282389) (by norm_num)
theorem B6346309 : Blo 1670035 6346309 := bbase (se 4 (by rfl) ⟨594966, by rfl⟩ : syracuseStep 6346309 = 1189933) (by norm_num)
theorem B3757661 : Blo 1670035 3757661 := bbase (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) (by norm_num)
theorem B5355109 : Blo 1670035 5355109 := bbase (se 4 (by rfl) ⟨502041, by rfl⟩ : syracuseStep 5355109 = 1004083) (by norm_num)
theorem B1783405 : Blo 1670035 1783405 := bbase (se 3 (by rfl) ⟨334388, by rfl⟩ : syracuseStep 1783405 = 668777) (by norm_num)
theorem B3053189 : Blo 1670035 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B3757733 : Blo 1670035 3757733 := bbase (se 4 (by rfl) ⟨352287, by rfl⟩ : syracuseStep 3757733 = 704575) (by norm_num)
theorem B6772405 : Blo 1670035 6772405 := bbase (se 5 (by rfl) ⟨317456, by rfl⟩ : syracuseStep 6772405 = 634913) (by norm_num)
theorem B12687029 : Blo 1670035 12687029 := bbase (se 5 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 12687029 = 1189409) (by norm_num)
theorem B3757805 : Blo 1670035 3757805 := bbase (se 3 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 3757805 = 1409177) (by norm_num)
theorem B5641973 : Blo 1670035 5641973 := bbase (se 5 (by rfl) ⟨264467, by rfl⟩ : syracuseStep 5641973 = 528935) (by norm_num)
theorem B3012365 : Blo 1670035 3012365 := bbase (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) (by norm_num)
theorem B6772501 : Blo 1670035 6772501 := bbase (se 6 (by rfl) ⟨158730, by rfl⟩ : syracuseStep 6772501 = 317461) (by norm_num)
theorem B3757877 : Blo 1670035 3757877 := bbase (se 5 (by rfl) ⟨176150, by rfl⟩ : syracuseStep 3757877 = 352301) (by norm_num)
theorem B2676581 : Blo 1670035 2676581 := bbase (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) (by norm_num)
theorem B6346613 : Blo 1670035 6346613 := bbase (se 5 (by rfl) ⟨297497, by rfl⟩ : syracuseStep 6346613 = 594995) (by norm_num)
theorem B3757949 : Blo 1670035 3757949 := bbase (se 3 (by rfl) ⟨704615, by rfl⟩ : syracuseStep 3757949 = 1409231) (by norm_num)
theorem B1906573 : Blo 1670035 1906573 := bbase (se 3 (by rfl) ⟨357482, by rfl⟩ : syracuseStep 1906573 = 714965) (by norm_num)
theorem B3094429 : Blo 1670035 3094429 := bbase (se 3 (by rfl) ⟨580205, by rfl⟩ : syracuseStep 3094429 = 1160411) (by norm_num)
theorem B3012509 : Blo 1670035 3012509 := bbase (se 3 (by rfl) ⟨564845, by rfl⟩ : syracuseStep 3012509 = 1129691) (by norm_num)
theorem B1783721 : Blo 1670035 1783721 := bbase (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) (by norm_num)
theorem B3758021 : Blo 1670035 3758021 := bbase (se 4 (by rfl) ⟨352314, by rfl⟩ : syracuseStep 3758021 = 704629) (by norm_num)
theorem B3569629 : Blo 1670035 3569629 := bbase (se 3 (by rfl) ⟨669305, by rfl⟩ : syracuseStep 3569629 = 1338611) (by norm_num)
theorem B3012589 : Blo 1670035 3012589 := bbase (se 3 (by rfl) ⟨564860, by rfl⟩ : syracuseStep 3012589 = 1129721) (by norm_num)
theorem B1693693 : Blo 1670035 1693693 := bbase (se 3 (by rfl) ⟨317567, by rfl⟩ : syracuseStep 1693693 = 635135) (by norm_num)
theorem B1906697 : Blo 1670035 1906697 := bbase (se 2 (by rfl) ⟨715011, by rfl⟩ : syracuseStep 1906697 = 1430023) (by norm_num)
theorem B3758093 : Blo 1670035 3758093 := bbase (se 3 (by rfl) ⟨704642, by rfl⟩ : syracuseStep 3758093 = 1409285) (by norm_num)
theorem B2857013 : Blo 1670035 2857013 := bbase (se 5 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 2857013 = 267845) (by norm_num)
theorem B7141445 : Blo 1670035 7141445 := bbase (se 4 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 7141445 = 1339021) (by norm_num)
theorem B3758165 : Blo 1670035 3758165 := bbase (se 8 (by rfl) ⟨22020, by rfl⟩ : syracuseStep 3758165 = 44041) (by norm_num)
theorem B4069493 : Blo 1670035 4069493 := bbase (se 5 (by rfl) ⟨190757, by rfl⟩ : syracuseStep 4069493 = 381515) (by norm_num)
theorem B3758237 : Blo 1670035 3758237 := bbase (se 3 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 3758237 = 1409339) (by norm_num)
theorem B5642405 : Blo 1670035 5642405 := bbase (se 4 (by rfl) ⟨528975, by rfl⟩ : syracuseStep 5642405 = 1057951) (by norm_num)
theorem B4757717 : Blo 1670035 4757717 := bbase (se 7 (by rfl) ⟨55754, by rfl⟩ : syracuseStep 4757717 = 111509) (by norm_num)
theorem B3758309 : Blo 1670035 3758309 := bbase (se 4 (by rfl) ⟨352341, by rfl⟩ : syracuseStep 3758309 = 704683) (by norm_num)
theorem B4348189 : Blo 1670035 4348189 := bbase (se 3 (by rfl) ⟨815285, by rfl⟩ : syracuseStep 4348189 = 1630571) (by norm_num)
theorem B2857253 : Blo 1670035 2857253 := bbase (se 4 (by rfl) ⟨267867, by rfl⟩ : syracuseStep 2857253 = 535735) (by norm_num)
theorem B3758381 : Blo 1670035 3758381 := bbase (se 3 (by rfl) ⟨704696, by rfl⟩ : syracuseStep 3758381 = 1409393) (by norm_num)
theorem B19298645 : Blo 1670035 19298645 := bbase (se 10 (by rfl) ⟨28269, by rfl⟩ : syracuseStep 19298645 = 56539) (by norm_num)
theorem B2505053 : Blo 1670035 2505053 := bbase (se 3 (by rfl) ⟨469697, by rfl⟩ : syracuseStep 2505053 = 939395) (by norm_num)
theorem B1784165 : Blo 1670035 1784165 := bbase (se 4 (by rfl) ⟨167265, by rfl⟩ : syracuseStep 1784165 = 334531) (by norm_num)
theorem B2677093 : Blo 1670035 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B2505077 : Blo 1670035 2505077 := bbase (se 5 (by rfl) ⟨117425, by rfl⟩ : syracuseStep 2505077 = 234851) (by norm_num)
theorem B3758453 : Blo 1670035 3758453 := bbase (se 5 (by rfl) ⟨176177, by rfl⟩ : syracuseStep 3758453 = 352355) (by norm_num)
theorem B2505101 : Blo 1670035 2505101 := bbase (se 3 (by rfl) ⟨469706, by rfl⟩ : syracuseStep 2505101 = 939413) (by norm_num)
theorem B1784225 : Blo 1670035 1784225 := bbase (se 2 (by rfl) ⟨669084, by rfl⟩ : syracuseStep 1784225 = 1338169) (by norm_num)
theorem B2505125 : Blo 1670035 2505125 := bbase (se 4 (by rfl) ⟨234855, by rfl⟩ : syracuseStep 2505125 = 469711) (by norm_num)
theorem B2505149 : Blo 1670035 2505149 := bbase (se 3 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 2505149 = 939431) (by norm_num)
theorem B3758525 : Blo 1670035 3758525 := bbase (se 3 (by rfl) ⟨704723, by rfl⟩ : syracuseStep 3758525 = 1409447) (by norm_num)
theorem B2505173 : Blo 1670035 2505173 := bbase (se 7 (by rfl) ⟨29357, by rfl⟩ : syracuseStep 2505173 = 58715) (by norm_num)
theorem B6019541 : Blo 1670035 6019541 := bbase (se 7 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 6019541 = 141083) (by norm_num)
theorem B1931749 : Blo 1670035 1931749 := bbase (se 4 (by rfl) ⟨181101, by rfl⟩ : syracuseStep 1931749 = 362203) (by norm_num)
theorem B8460773 : Blo 1670035 8460773 := bbase (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) (by norm_num)
theorem B2505197 : Blo 1670035 2505197 := bbase (se 3 (by rfl) ⟨469724, by rfl⟩ : syracuseStep 2505197 = 939449) (by norm_num)
theorem B2505221 : Blo 1670035 2505221 := bbase (se 4 (by rfl) ⟨234864, by rfl⟩ : syracuseStep 2505221 = 469729) (by norm_num)
theorem B3758597 : Blo 1670035 3758597 := bbase (se 4 (by rfl) ⟨352368, by rfl⟩ : syracuseStep 3758597 = 704737) (by norm_num)
theorem B2505245 : Blo 1670035 2505245 := bbase (se 3 (by rfl) ⟨469733, by rfl⟩ : syracuseStep 2505245 = 939467) (by norm_num)
theorem B1784353 : Blo 1670035 1784353 := bbase (se 2 (by rfl) ⟨669132, by rfl⟩ : syracuseStep 1784353 = 1338265) (by norm_num)
theorem B2505269 : Blo 1670035 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B2505293 : Blo 1670035 2505293 := bbase (se 3 (by rfl) ⟨469742, by rfl⟩ : syracuseStep 2505293 = 939485) (by norm_num)
theorem B3758669 : Blo 1670035 3758669 := bbase (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) (by norm_num)
theorem B2259533 : Blo 1670035 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B5642837 : Blo 1670035 5642837 := bbase (se 8 (by rfl) ⟨33063, by rfl⟩ : syracuseStep 5642837 = 66127) (by norm_num)
theorem B2505317 : Blo 1670035 2505317 := bbase (se 4 (by rfl) ⟨234873, by rfl⟩ : syracuseStep 2505317 = 469747) (by norm_num)
theorem B2505341 : Blo 1670035 2505341 := bbase (se 3 (by rfl) ⟨469751, by rfl⟩ : syracuseStep 2505341 = 939503) (by norm_num)
theorem B2505365 : Blo 1670035 2505365 := bbase (se 6 (by rfl) ⟨58719, by rfl⟩ : syracuseStep 2505365 = 117439) (by norm_num)
theorem B3758741 : Blo 1670035 3758741 := bbase (se 6 (by rfl) ⟨88095, by rfl⟩ : syracuseStep 3758741 = 176191) (by norm_num)
theorem B8575637 : Blo 1670035 8575637 := bbase (se 6 (by rfl) ⟨200991, by rfl⟩ : syracuseStep 8575637 = 401983) (by norm_num)
theorem B2505389 : Blo 1670035 2505389 := bbase (se 3 (by rfl) ⟨469760, by rfl⟩ : syracuseStep 2505389 = 939521) (by norm_num)
theorem B2505413 : Blo 1670035 2505413 := bbase (se 4 (by rfl) ⟨234882, by rfl⟩ : syracuseStep 2505413 = 469765) (by norm_num)
theorem B2505437 : Blo 1670035 2505437 := bbase (se 3 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 2505437 = 939539) (by norm_num)
theorem B3758813 : Blo 1670035 3758813 := bbase (se 3 (by rfl) ⟨704777, by rfl⟩ : syracuseStep 3758813 = 1409555) (by norm_num)
theorem B2505461 : Blo 1670035 2505461 := bbase (se 5 (by rfl) ⟨117443, by rfl⟩ : syracuseStep 2505461 = 234887) (by norm_num)
theorem B2505485 : Blo 1670035 2505485 := bbase (se 3 (by rfl) ⟨469778, by rfl⟩ : syracuseStep 2505485 = 939557) (by norm_num)
theorem B2505509 : Blo 1670035 2505509 := bbase (se 4 (by rfl) ⟨234891, by rfl⟩ : syracuseStep 2505509 = 469783) (by norm_num)
theorem B3758885 : Blo 1670035 3758885 := bbase (se 4 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 3758885 = 704791) (by norm_num)
theorem B2677549 : Blo 1670035 2677549 := bbase (se 3 (by rfl) ⟨502040, by rfl⟩ : syracuseStep 2677549 = 1004081) (by norm_num)
theorem B2505533 : Blo 1670035 2505533 := bbase (se 3 (by rfl) ⟨469787, by rfl⟩ : syracuseStep 2505533 = 939575) (by norm_num)
theorem B2505557 : Blo 1670035 2505557 := bbase (se 9 (by rfl) ⟨7340, by rfl⟩ : syracuseStep 2505557 = 14681) (by norm_num)
theorem B3570517 : Blo 1670035 3570517 := bbase (se 9 (by rfl) ⟨10460, by rfl⟩ : syracuseStep 3570517 = 20921) (by norm_num)
theorem B2505581 : Blo 1670035 2505581 := bbase (se 3 (by rfl) ⟨469796, by rfl⟩ : syracuseStep 2505581 = 939593) (by norm_num)
theorem B3758957 : Blo 1670035 3758957 := bbase (se 3 (by rfl) ⟨704804, by rfl⟩ : syracuseStep 3758957 = 1409609) (by norm_num)
theorem B4758389 : Blo 1670035 4758389 := bbase (se 5 (by rfl) ⟨223049, by rfl⟩ : syracuseStep 4758389 = 446099) (by norm_num)
theorem B2505605 : Blo 1670035 2505605 := bbase (se 4 (by rfl) ⟨234900, by rfl⟩ : syracuseStep 2505605 = 469801) (by norm_num)
theorem B4012949 : Blo 1670035 4012949 := bbase (se 6 (by rfl) ⟨94053, by rfl⟩ : syracuseStep 4012949 = 188107) (by norm_num)
theorem B1694617 : Blo 1670035 1694617 := bbase (se 2 (by rfl) ⟨635481, by rfl⟩ : syracuseStep 1694617 = 1270963) (by norm_num)
theorem B2505629 : Blo 1670035 2505629 := bbase (se 3 (by rfl) ⟨469805, by rfl⟩ : syracuseStep 2505629 = 939611) (by norm_num)
theorem B2505653 : Blo 1670035 2505653 := bbase (se 5 (by rfl) ⟨117452, by rfl⟩ : syracuseStep 2505653 = 234905) (by norm_num)
theorem B3759029 : Blo 1670035 3759029 := bbase (se 5 (by rfl) ⟨176204, by rfl⟩ : syracuseStep 3759029 = 352409) (by norm_num)
theorem B5356469 : Blo 1670035 5356469 := bbase (se 5 (by rfl) ⟨251084, by rfl⟩ : syracuseStep 5356469 = 502169) (by norm_num)
theorem B2505677 : Blo 1670035 2505677 := bbase (se 3 (by rfl) ⟨469814, by rfl⟩ : syracuseStep 2505677 = 939629) (by norm_num)
theorem B3570637 : Blo 1670035 3570637 := bbase (se 3 (by rfl) ⟨669494, by rfl⟩ : syracuseStep 3570637 = 1338989) (by norm_num)
theorem B1784797 : Blo 1670035 1784797 := bbase (se 3 (by rfl) ⟨334649, by rfl⟩ : syracuseStep 1784797 = 669299) (by norm_num)
theorem B2505701 : Blo 1670035 2505701 := bbase (se 4 (by rfl) ⟨234909, by rfl⟩ : syracuseStep 2505701 = 469819) (by norm_num)
theorem B2505725 : Blo 1670035 2505725 := bbase (se 3 (by rfl) ⟨469823, by rfl⟩ : syracuseStep 2505725 = 939647) (by norm_num)
theorem B3759101 : Blo 1670035 3759101 := bbase (se 3 (by rfl) ⟨704831, by rfl⟩ : syracuseStep 3759101 = 1409663) (by norm_num)
theorem B2505749 : Blo 1670035 2505749 := bbase (se 6 (by rfl) ⟨58728, by rfl⟩ : syracuseStep 2505749 = 117457) (by norm_num)
theorem B6773797 : Blo 1670035 6773797 := bbase (se 4 (by rfl) ⟨635043, by rfl⟩ : syracuseStep 6773797 = 1270087) (by norm_num)
theorem B2505773 : Blo 1670035 2505773 := bbase (se 3 (by rfl) ⟨469832, by rfl⟩ : syracuseStep 2505773 = 939665) (by norm_num)
theorem B2505797 : Blo 1670035 2505797 := bbase (se 4 (by rfl) ⟨234918, by rfl⟩ : syracuseStep 2505797 = 469837) (by norm_num)
theorem B3759173 : Blo 1670035 3759173 := bbase (se 4 (by rfl) ⟨352422, by rfl⟩ : syracuseStep 3759173 = 704845) (by norm_num)
theorem B2858053 : Blo 1670035 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B1784917 : Blo 1670035 1784917 := bbase (se 8 (by rfl) ⟨10458, by rfl⟩ : syracuseStep 1784917 = 20917) (by norm_num)
theorem B2505821 : Blo 1670035 2505821 := bbase (se 3 (by rfl) ⟨469841, by rfl⟩ : syracuseStep 2505821 = 939683) (by norm_num)
theorem B2505845 : Blo 1670035 2505845 := bbase (se 5 (by rfl) ⟨117461, by rfl⟩ : syracuseStep 2505845 = 234923) (by norm_num)
theorem B2505869 : Blo 1670035 2505869 := bbase (se 3 (by rfl) ⟨469850, by rfl⟩ : syracuseStep 2505869 = 939701) (by norm_num)
theorem B3759245 : Blo 1670035 3759245 := bbase (se 3 (by rfl) ⟨704858, by rfl⟩ : syracuseStep 3759245 = 1409717) (by norm_num)
theorem B2505893 : Blo 1670035 2505893 := bbase (se 4 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 2505893 = 469855) (by norm_num)
theorem B7134389 : Blo 1670035 7134389 := bbase (se 5 (by rfl) ⟨334424, by rfl⟩ : syracuseStep 7134389 = 668849) (by norm_num)
theorem B2505917 : Blo 1670035 2505917 := bbase (se 3 (by rfl) ⟨469859, by rfl⟩ : syracuseStep 2505917 = 939719) (by norm_num)
theorem B3570893 : Blo 1670035 3570893 := bbase (se 3 (by rfl) ⟨669542, by rfl⟩ : syracuseStep 3570893 = 1339085) (by norm_num)
theorem B2505941 : Blo 1670035 2505941 := bbase (se 7 (by rfl) ⟨29366, by rfl⟩ : syracuseStep 2505941 = 58733) (by norm_num)
theorem B3759317 : Blo 1670035 3759317 := bbase (se 7 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 3759317 = 88109) (by norm_num)
theorem B2505965 : Blo 1670035 2505965 := bbase (se 3 (by rfl) ⟨469868, by rfl⟩ : syracuseStep 2505965 = 939737) (by norm_num)
theorem B2505989 : Blo 1670035 2505989 := bbase (se 4 (by rfl) ⟨234936, by rfl⟩ : syracuseStep 2505989 = 469873) (by norm_num)
theorem B2506013 : Blo 1670035 2506013 := bbase (se 3 (by rfl) ⟨469877, by rfl⟩ : syracuseStep 2506013 = 939755) (by norm_num)
theorem B3759389 : Blo 1670035 3759389 := bbase (se 3 (by rfl) ⟨704885, by rfl⟩ : syracuseStep 3759389 = 1409771) (by norm_num)
theorem B4758821 : Blo 1670035 4758821 := bbase (se 4 (by rfl) ⟨446139, by rfl⟩ : syracuseStep 4758821 = 892279) (by norm_num)
theorem B2506037 : Blo 1670035 2506037 := bbase (se 5 (by rfl) ⟨117470, by rfl⟩ : syracuseStep 2506037 = 234941) (by norm_num)
theorem B2506061 : Blo 1670035 2506061 := bbase (se 3 (by rfl) ⟨469886, by rfl⟩ : syracuseStep 2506061 = 939773) (by norm_num)
theorem B1785169 : Blo 1670035 1785169 := bbase (se 2 (by rfl) ⟨669438, by rfl⟩ : syracuseStep 1785169 = 1338877) (by norm_num)
theorem B1785173 : Blo 1670035 1785173 := bbase (se 11 (by rfl) ⟨1307, by rfl⟩ : syracuseStep 1785173 = 2615) (by norm_num)
theorem B2506085 : Blo 1670035 2506085 := bbase (se 4 (by rfl) ⟨234945, by rfl⟩ : syracuseStep 2506085 = 469891) (by norm_num)
theorem B3759461 : Blo 1670035 3759461 := bbase (se 4 (by rfl) ⟨352449, by rfl⟩ : syracuseStep 3759461 = 704899) (by norm_num)
theorem B2506109 : Blo 1670035 2506109 := bbase (se 3 (by rfl) ⟨469895, by rfl⟩ : syracuseStep 2506109 = 939791) (by norm_num)
theorem B2006417 : Blo 1670035 2006417 := bbase (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) (by norm_num)
theorem B2506133 : Blo 1670035 2506133 := bbase (se 6 (by rfl) ⟨58737, by rfl⟩ : syracuseStep 2506133 = 117475) (by norm_num)
theorem B2506157 : Blo 1670035 2506157 := bbase (se 3 (by rfl) ⟨469904, by rfl⟩ : syracuseStep 2506157 = 939809) (by norm_num)
theorem B3759533 : Blo 1670035 3759533 := bbase (se 3 (by rfl) ⟨704912, by rfl⟩ : syracuseStep 3759533 = 1409825) (by norm_num)
theorem B2506181 : Blo 1670035 2506181 := bbase (se 4 (by rfl) ⟨234954, by rfl⟩ : syracuseStep 2506181 = 469909) (by norm_num)
theorem B2678221 : Blo 1670035 2678221 := bbase (se 3 (by rfl) ⟨502166, by rfl⟩ : syracuseStep 2678221 = 1004333) (by norm_num)
theorem B2506205 : Blo 1670035 2506205 := bbase (se 3 (by rfl) ⟨469913, by rfl⟩ : syracuseStep 2506205 = 939827) (by norm_num)
theorem B2506229 : Blo 1670035 2506229 := bbase (se 5 (by rfl) ⟨117479, by rfl⟩ : syracuseStep 2506229 = 234959) (by norm_num)
theorem B3759605 : Blo 1670035 3759605 := bbase (se 5 (by rfl) ⟨176231, by rfl⟩ : syracuseStep 3759605 = 352463) (by norm_num)
theorem B2506253 : Blo 1670035 2506253 := bbase (se 3 (by rfl) ⟨469922, by rfl⟩ : syracuseStep 2506253 = 939845) (by norm_num)
theorem B2506277 : Blo 1670035 2506277 := bbase (se 4 (by rfl) ⟨234963, by rfl⟩ : syracuseStep 2506277 = 469927) (by norm_num)
theorem B2506301 : Blo 1670035 2506301 := bbase (se 3 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 2506301 = 939863) (by norm_num)
theorem B3759677 : Blo 1670035 3759677 := bbase (se 3 (by rfl) ⟨704939, by rfl⟩ : syracuseStep 3759677 = 1409879) (by norm_num)
theorem B6020693 : Blo 1670035 6020693 := bbase (se 8 (by rfl) ⟨35277, by rfl⟩ : syracuseStep 6020693 = 70555) (by norm_num)
theorem B2506325 : Blo 1670035 2506325 := bbase (se 8 (by rfl) ⟨14685, by rfl⟩ : syracuseStep 2506325 = 29371) (by norm_num)
theorem B2506349 : Blo 1670035 2506349 := bbase (se 3 (by rfl) ⟨469940, by rfl⟩ : syracuseStep 2506349 = 939881) (by norm_num)
theorem B2506373 : Blo 1670035 2506373 := bbase (se 4 (by rfl) ⟨234972, by rfl⟩ : syracuseStep 2506373 = 469945) (by norm_num)
theorem B3759749 : Blo 1670035 3759749 := bbase (se 4 (by rfl) ⟨352476, by rfl⟩ : syracuseStep 3759749 = 704953) (by norm_num)
theorem B2506397 : Blo 1670035 2506397 := bbase (se 3 (by rfl) ⟨469949, by rfl⟩ : syracuseStep 2506397 = 939899) (by norm_num)
theorem B2506421 : Blo 1670035 2506421 := bbase (se 5 (by rfl) ⟨117488, by rfl⟩ : syracuseStep 2506421 = 234977) (by norm_num)
theorem B2506445 : Blo 1670035 2506445 := bbase (se 3 (by rfl) ⟨469958, by rfl⟩ : syracuseStep 2506445 = 939917) (by norm_num)
theorem B3759821 : Blo 1670035 3759821 := bbase (se 3 (by rfl) ⟨704966, by rfl⟩ : syracuseStep 3759821 = 1409933) (by norm_num)
theorem B2506469 : Blo 1670035 2506469 := bbase (se 4 (by rfl) ⟨234981, by rfl⟩ : syracuseStep 2506469 = 469963) (by norm_num)
theorem B8462069 : Blo 1670035 8462069 := bbase (se 5 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 8462069 = 793319) (by norm_num)
theorem B2506493 : Blo 1670035 2506493 := bbase (se 3 (by rfl) ⟨469967, by rfl⟩ : syracuseStep 2506493 = 939935) (by norm_num)
theorem B2506517 : Blo 1670035 2506517 := bbase (se 6 (by rfl) ⟨58746, by rfl⟩ : syracuseStep 2506517 = 117493) (by norm_num)
theorem B3759893 : Blo 1670035 3759893 := bbase (se 6 (by rfl) ⟨88122, by rfl⟩ : syracuseStep 3759893 = 176245) (by norm_num)
theorem B2506541 : Blo 1670035 2506541 := bbase (se 3 (by rfl) ⟨469976, by rfl⟩ : syracuseStep 2506541 = 939953) (by norm_num)
theorem B2506565 : Blo 1670035 2506565 := bbase (se 4 (by rfl) ⟨234990, by rfl⟩ : syracuseStep 2506565 = 469981) (by norm_num)
theorem B2506589 : Blo 1670035 2506589 := bbase (se 3 (by rfl) ⟨469985, by rfl⟩ : syracuseStep 2506589 = 939971) (by norm_num)
theorem B3759965 : Blo 1670035 3759965 := bbase (se 3 (by rfl) ⟨704993, by rfl⟩ : syracuseStep 3759965 = 1409987) (by norm_num)
theorem B2506613 : Blo 1670035 2506613 := bbase (se 5 (by rfl) ⟨117497, by rfl⟩ : syracuseStep 2506613 = 234995) (by norm_num)
theorem B2506637 : Blo 1670035 2506637 := bbase (se 3 (by rfl) ⟨469994, by rfl⟩ : syracuseStep 2506637 = 939989) (by norm_num)
theorem B16064405 : Blo 1670035 16064405 := bbase (se 6 (by rfl) ⟨376509, by rfl⟩ : syracuseStep 16064405 = 753019) (by norm_num)
theorem B2506661 : Blo 1670035 2506661 := bbase (se 4 (by rfl) ⟨234999, by rfl⟩ : syracuseStep 2506661 = 469999) (by norm_num)
theorem B3760037 : Blo 1670035 3760037 := bbase (se 4 (by rfl) ⟨352503, by rfl⟩ : syracuseStep 3760037 = 705007) (by norm_num)
theorem B2506685 : Blo 1670035 2506685 := bbase (se 3 (by rfl) ⟨470003, by rfl⟩ : syracuseStep 2506685 = 940007) (by norm_num)
theorem B2506709 : Blo 1670035 2506709 := bbase (se 7 (by rfl) ⟨29375, by rfl⟩ : syracuseStep 2506709 = 58751) (by norm_num)
theorem B2007013 : Blo 1670035 2007013 := bbase (se 4 (by rfl) ⟨188157, by rfl⟩ : syracuseStep 2007013 = 376315) (by norm_num)
theorem B2506733 : Blo 1670035 2506733 := bbase (se 3 (by rfl) ⟨470012, by rfl⟩ : syracuseStep 2506733 = 940025) (by norm_num)
theorem B3760109 : Blo 1670035 3760109 := bbase (se 3 (by rfl) ⟨705020, by rfl⟩ : syracuseStep 3760109 = 1410041) (by norm_num)
theorem B1671171 : Blo 1670035 1671171 := bstep (se 1 (by rfl) ⟨1253378, by rfl⟩ : syracuseStep 1671171 = 2506757) B2506757
theorem B3760145 : Blo 1670035 3760145 := bstep (se 2 (by rfl) ⟨1410054, by rfl⟩ : syracuseStep 3760145 = 2820109) B2820109
theorem B2506769 : Blo 1670035 2506769 := bstep (se 2 (by rfl) ⟨940038, by rfl⟩ : syracuseStep 2506769 = 1880077) B1880077
theorem B1671187 : Blo 1670035 1671187 := bstep (se 1 (by rfl) ⟨1253390, by rfl⟩ : syracuseStep 1671187 = 2506781) B2506781
theorem B3760163 : Blo 1670035 3760163 := bstep (se 1 (by rfl) ⟨2820122, by rfl⟩ : syracuseStep 3760163 = 5640245) B5640245
theorem B2506787 : Blo 1670035 2506787 := bstep (se 1 (by rfl) ⟨1880090, by rfl⟩ : syracuseStep 2506787 = 3760181) B3760181
theorem B1671203 : Blo 1670035 1671203 := bstep (se 1 (by rfl) ⟨1253402, by rfl⟩ : syracuseStep 1671203 = 2506805) B2506805
theorem B1671219 : Blo 1670035 1671219 := bstep (se 1 (by rfl) ⟨1253414, by rfl⟩ : syracuseStep 1671219 = 2506829) B2506829
theorem B2506817 : Blo 1670035 2506817 := bstep (se 2 (by rfl) ⟨940056, by rfl⟩ : syracuseStep 2506817 = 1880113) B1880113
theorem B1671235 : Blo 1670035 1671235 := bstep (se 1 (by rfl) ⟨1253426, by rfl⟩ : syracuseStep 1671235 = 2506853) B2506853
theorem B2506835 : Blo 1670035 2506835 := bstep (se 1 (by rfl) ⟨1880126, by rfl⟩ : syracuseStep 2506835 = 3760253) B3760253
theorem B1671251 : Blo 1670035 1671251 := bstep (se 1 (by rfl) ⟨1253438, by rfl⟩ : syracuseStep 1671251 = 2506877) B2506877
theorem B1671267 : Blo 1670035 1671267 := bstep (se 1 (by rfl) ⟨1253450, by rfl⟩ : syracuseStep 1671267 = 2506901) B2506901
theorem B2506865 : Blo 1670035 2506865 := bstep (se 2 (by rfl) ⟨940074, by rfl⟩ : syracuseStep 2506865 = 1880149) B1880149
theorem B1671283 : Blo 1670035 1671283 := bstep (se 1 (by rfl) ⟨1253462, by rfl⟩ : syracuseStep 1671283 = 2506925) B2506925
theorem B2506883 : Blo 1670035 2506883 := bstep (se 1 (by rfl) ⟨1880162, by rfl⟩ : syracuseStep 2506883 = 3760325) B3760325
theorem B1671299 : Blo 1670035 1671299 := bstep (se 1 (by rfl) ⟨1253474, by rfl⟩ : syracuseStep 1671299 = 2506949) B2506949
theorem B5079181 : Blo 1670035 5079181 := bstep (se 3 (by rfl) ⟨952346, by rfl⟩ : syracuseStep 5079181 = 1904693) B1904693
theorem B1671315 : Blo 1670035 1671315 := bstep (se 1 (by rfl) ⟨1253486, by rfl⟩ : syracuseStep 1671315 = 2506973) B2506973
theorem B2506913 : Blo 1670035 2506913 := bstep (se 2 (by rfl) ⟨940092, by rfl⟩ : syracuseStep 2506913 = 1880185) B1880185
theorem B1671331 : Blo 1670035 1671331 := bstep (se 1 (by rfl) ⟨1253498, by rfl⟩ : syracuseStep 1671331 = 2506997) B2506997
theorem B2113715 : Blo 1670035 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B2506931 : Blo 1670035 2506931 := bstep (se 1 (by rfl) ⟨1880198, by rfl⟩ : syracuseStep 2506931 = 3760397) B3760397
theorem B1671347 : Blo 1670035 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B1671363 : Blo 1670035 1671363 := bstep (se 1 (by rfl) ⟨1253522, by rfl⟩ : syracuseStep 1671363 = 2507045) B2507045
theorem B36126917 : Blo 1670035 36126917 := bstep (se 4 (by rfl) ⟨3386898, by rfl⟩ : syracuseStep 36126917 = 6773797) B6773797
theorem B2506961 : Blo 1670035 2506961 := bstep (se 2 (by rfl) ⟨940110, by rfl⟩ : syracuseStep 2506961 = 1880221) B1880221
theorem B1671379 : Blo 1670035 1671379 := bstep (se 1 (by rfl) ⟨1253534, by rfl⟩ : syracuseStep 1671379 = 2507069) B2507069
theorem B2818273 : Blo 1670035 2818273 := bstep (se 2 (by rfl) ⟨1056852, by rfl⟩ : syracuseStep 2818273 = 2113705) B2113705
theorem B4227299 : Blo 1670035 4227299 := bstep (se 1 (by rfl) ⟨3170474, by rfl⟩ : syracuseStep 4227299 = 6340949) B6340949
theorem B2506979 : Blo 1670035 2506979 := bstep (se 1 (by rfl) ⟨1880234, by rfl⟩ : syracuseStep 2506979 = 3760469) B3760469
theorem B1671395 : Blo 1670035 1671395 := bstep (se 1 (by rfl) ⟨1253546, by rfl⟩ : syracuseStep 1671395 = 2507093) B2507093
theorem B1671411 : Blo 1670035 1671411 := bstep (se 1 (by rfl) ⟨1253558, by rfl⟩ : syracuseStep 1671411 = 2507117) B2507117
theorem B2507009 : Blo 1670035 2507009 := bstep (se 2 (by rfl) ⟨940128, by rfl⟩ : syracuseStep 2507009 = 1880257) B1880257
theorem B2818307 : Blo 1670035 2818307 := bstep (se 1 (by rfl) ⟨2113730, by rfl⟩ : syracuseStep 2818307 = 4227461) B4227461
theorem B1671427 : Blo 1670035 1671427 := bstep (se 1 (by rfl) ⟨1253570, by rfl⟩ : syracuseStep 1671427 = 2507141) B2507141
theorem B4014353 : Blo 1670035 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B2507027 : Blo 1670035 2507027 := bstep (se 1 (by rfl) ⟨1880270, by rfl⟩ : syracuseStep 2507027 = 3760541) B3760541
theorem B1671443 : Blo 1670035 1671443 := bstep (se 1 (by rfl) ⟨1253582, by rfl⟩ : syracuseStep 1671443 = 2507165) B2507165
theorem B1671459 : Blo 1670035 1671459 := bstep (se 1 (by rfl) ⟨1253594, by rfl⟩ : syracuseStep 1671459 = 2507189) B2507189
theorem B3760433 : Blo 1670035 3760433 := bstep (se 2 (by rfl) ⟨1410162, by rfl⟩ : syracuseStep 3760433 = 2820325) B2820325
theorem B2507057 : Blo 1670035 2507057 := bstep (se 2 (by rfl) ⟨940146, by rfl⟩ : syracuseStep 2507057 = 1880293) B1880293
theorem B1671475 : Blo 1670035 1671475 := bstep (se 1 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 1671475 = 2507213) B2507213
theorem B3760451 : Blo 1670035 3760451 := bstep (se 1 (by rfl) ⟨2820338, by rfl⟩ : syracuseStep 3760451 = 5640677) B5640677
theorem B2507075 : Blo 1670035 2507075 := bstep (se 1 (by rfl) ⟨1880306, by rfl⟩ : syracuseStep 2507075 = 3760613) B3760613
theorem B1671491 : Blo 1670035 1671491 := bstep (se 1 (by rfl) ⟨1253618, by rfl⟩ : syracuseStep 1671491 = 2507237) B2507237
theorem B1671507 : Blo 1670035 1671507 := bstep (se 1 (by rfl) ⟨1253630, by rfl⟩ : syracuseStep 1671507 = 2507261) B2507261
theorem B2507105 : Blo 1670035 2507105 := bstep (se 2 (by rfl) ⟨940164, by rfl⟩ : syracuseStep 2507105 = 1880329) B1880329
theorem B6340963 : Blo 1670035 6340963 := bstep (se 1 (by rfl) ⟨4755722, by rfl⟩ : syracuseStep 6340963 = 9511445) B9511445
theorem B19038563 : Blo 1670035 19038563 := bstep (se 1 (by rfl) ⟨14278922, by rfl⟩ : syracuseStep 19038563 = 28557845) B28557845
theorem B1671523 : Blo 1670035 1671523 := bstep (se 1 (by rfl) ⟨1253642, by rfl⟩ : syracuseStep 1671523 = 2507285) B2507285
theorem B5636465 : Blo 1670035 5636465 := bstep (se 2 (by rfl) ⟨2113674, by rfl⟩ : syracuseStep 5636465 = 4227349) B4227349
theorem B2507123 : Blo 1670035 2507123 := bstep (se 1 (by rfl) ⟨1880342, by rfl⟩ : syracuseStep 2507123 = 3760685) B3760685
theorem B1671539 : Blo 1670035 1671539 := bstep (se 1 (by rfl) ⟨1253654, by rfl⟩ : syracuseStep 1671539 = 2507309) B2507309
theorem B2818435 : Blo 1670035 2818435 := bstep (se 1 (by rfl) ⟨2113826, by rfl⟩ : syracuseStep 2818435 = 4227653) B4227653
theorem B1671555 : Blo 1670035 1671555 := bstep (se 1 (by rfl) ⟨1253666, by rfl⟩ : syracuseStep 1671555 = 2507333) B2507333
theorem B2507153 : Blo 1670035 2507153 := bstep (se 2 (by rfl) ⟨940182, by rfl⟩ : syracuseStep 2507153 = 1880365) B1880365
theorem B1671571 : Blo 1670035 1671571 := bstep (se 1 (by rfl) ⟨1253678, by rfl⟩ : syracuseStep 1671571 = 2507357) B2507357
theorem B4227491 : Blo 1670035 4227491 := bstep (se 1 (by rfl) ⟨3170618, by rfl⟩ : syracuseStep 4227491 = 6341237) B6341237
theorem B2507171 : Blo 1670035 2507171 := bstep (se 1 (by rfl) ⟨1880378, by rfl⟩ : syracuseStep 2507171 = 3760757) B3760757
theorem B1671587 : Blo 1670035 1671587 := bstep (se 1 (by rfl) ⟨1253690, by rfl⟩ : syracuseStep 1671587 = 2507381) B2507381
theorem B1671603 : Blo 1670035 1671603 := bstep (se 1 (by rfl) ⟨1253702, by rfl⟩ : syracuseStep 1671603 = 2507405) B2507405
theorem B3170755 : Blo 1670035 3170755 := bstep (se 1 (by rfl) ⟨2378066, by rfl⟩ : syracuseStep 3170755 = 4756133) B4756133
theorem B2507201 : Blo 1670035 2507201 := bstep (se 2 (by rfl) ⟨940200, by rfl⟩ : syracuseStep 2507201 = 1880401) B1880401
theorem B1671619 : Blo 1670035 1671619 := bstep (se 1 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 1671619 = 2507429) B2507429
theorem B2507219 : Blo 1670035 2507219 := bstep (se 1 (by rfl) ⟨1880414, by rfl⟩ : syracuseStep 2507219 = 3760829) B3760829
theorem B1671635 : Blo 1670035 1671635 := bstep (se 1 (by rfl) ⟨1253726, by rfl⟩ : syracuseStep 1671635 = 2507453) B2507453
theorem B1671651 : Blo 1670035 1671651 := bstep (se 1 (by rfl) ⟨1253738, by rfl⟩ : syracuseStep 1671651 = 2507477) B2507477
theorem B3170801 : Blo 1670035 3170801 := bstep (se 2 (by rfl) ⟨1189050, by rfl⟩ : syracuseStep 3170801 = 2378101) B2378101
theorem B2507249 : Blo 1670035 2507249 := bstep (se 2 (by rfl) ⟨940218, by rfl⟩ : syracuseStep 2507249 = 1880437) B1880437
theorem B1671667 : Blo 1670035 1671667 := bstep (se 1 (by rfl) ⟨1253750, by rfl⟩ : syracuseStep 1671667 = 2507501) B2507501
theorem B2507267 : Blo 1670035 2507267 := bstep (se 1 (by rfl) ⟨1880450, by rfl⟩ : syracuseStep 2507267 = 3760901) B3760901
theorem B1671683 : Blo 1670035 1671683 := bstep (se 1 (by rfl) ⟨1253762, by rfl⟩ : syracuseStep 1671683 = 2507525) B2507525
theorem B2818577 : Blo 1670035 2818577 := bstep (se 2 (by rfl) ⟨1056966, by rfl⟩ : syracuseStep 2818577 = 2113933) B2113933
theorem B1671699 : Blo 1670035 1671699 := bstep (se 1 (by rfl) ⟨1253774, by rfl⟩ : syracuseStep 1671699 = 2507549) B2507549
theorem B2507297 : Blo 1670035 2507297 := bstep (se 2 (by rfl) ⟨940236, by rfl⟩ : syracuseStep 2507297 = 1880473) B1880473
theorem B1671715 : Blo 1670035 1671715 := bstep (se 1 (by rfl) ⟨1253786, by rfl⟩ : syracuseStep 1671715 = 2507573) B2507573
theorem B2507315 : Blo 1670035 2507315 := bstep (se 1 (by rfl) ⟨1880486, by rfl⟩ : syracuseStep 2507315 = 3760973) B3760973
theorem B1671731 : Blo 1670035 1671731 := bstep (se 1 (by rfl) ⟨1253798, by rfl⟩ : syracuseStep 1671731 = 2507597) B2507597
theorem B1671747 : Blo 1670035 1671747 := bstep (se 1 (by rfl) ⟨1253810, by rfl⟩ : syracuseStep 1671747 = 2507621) B2507621
theorem B3760721 : Blo 1670035 3760721 := bstep (se 2 (by rfl) ⟨1410270, by rfl⟩ : syracuseStep 3760721 = 2820541) B2820541
theorem B2507345 : Blo 1670035 2507345 := bstep (se 2 (by rfl) ⟨940254, by rfl⟩ : syracuseStep 2507345 = 1880509) B1880509
theorem B1671763 : Blo 1670035 1671763 := bstep (se 1 (by rfl) ⟨1253822, by rfl⟩ : syracuseStep 1671763 = 2507645) B2507645
theorem B3760739 : Blo 1670035 3760739 := bstep (se 1 (by rfl) ⟨2820554, by rfl⟩ : syracuseStep 3760739 = 5641109) B5641109
theorem B2507363 : Blo 1670035 2507363 := bstep (se 1 (by rfl) ⟨1880522, by rfl⟩ : syracuseStep 2507363 = 3761045) B3761045
theorem B1671779 : Blo 1670035 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B1671795 : Blo 1670035 1671795 := bstep (se 1 (by rfl) ⟨1253846, by rfl⟩ : syracuseStep 1671795 = 2507693) B2507693
theorem B2507393 : Blo 1670035 2507393 := bstep (se 2 (by rfl) ⟨940272, by rfl⟩ : syracuseStep 2507393 = 1880545) B1880545
theorem B1671811 : Blo 1670035 1671811 := bstep (se 1 (by rfl) ⟨1253858, by rfl⟩ : syracuseStep 1671811 = 2507717) B2507717
theorem B2818705 : Blo 1670035 2818705 := bstep (se 2 (by rfl) ⟨1057014, by rfl⟩ : syracuseStep 2818705 = 2114029) B2114029
theorem B2507411 : Blo 1670035 2507411 := bstep (se 1 (by rfl) ⟨1880558, by rfl⟩ : syracuseStep 2507411 = 3761117) B3761117
theorem B1671827 : Blo 1670035 1671827 := bstep (se 1 (by rfl) ⟨1253870, by rfl⟩ : syracuseStep 1671827 = 2507741) B2507741
theorem B1671843 : Blo 1670035 1671843 := bstep (se 1 (by rfl) ⟨1253882, by rfl⟩ : syracuseStep 1671843 = 2507765) B2507765
theorem B2507441 : Blo 1670035 2507441 := bstep (se 2 (by rfl) ⟨940290, by rfl⟩ : syracuseStep 2507441 = 1880581) B1880581
theorem B2818739 : Blo 1670035 2818739 := bstep (se 1 (by rfl) ⟨2114054, by rfl⟩ : syracuseStep 2818739 = 4228109) B4228109
theorem B1671859 : Blo 1670035 1671859 := bstep (se 1 (by rfl) ⟨1253894, by rfl⟩ : syracuseStep 1671859 = 2507789) B2507789
theorem B2507459 : Blo 1670035 2507459 := bstep (se 1 (by rfl) ⟨1880594, by rfl⟩ : syracuseStep 2507459 = 3761189) B3761189
theorem B1671875 : Blo 1670035 1671875 := bstep (se 1 (by rfl) ⟨1253906, by rfl⟩ : syracuseStep 1671875 = 2507813) B2507813
theorem B1671891 : Blo 1670035 1671891 := bstep (se 1 (by rfl) ⟨1253918, by rfl⟩ : syracuseStep 1671891 = 2507837) B2507837
theorem B2507489 : Blo 1670035 2507489 := bstep (se 2 (by rfl) ⟨940308, by rfl⟩ : syracuseStep 2507489 = 1880617) B1880617
theorem B1671907 : Blo 1670035 1671907 := bstep (se 1 (by rfl) ⟨1253930, by rfl⟩ : syracuseStep 1671907 = 2507861) B2507861
theorem B2507507 : Blo 1670035 2507507 := bstep (se 1 (by rfl) ⟨1880630, by rfl⟩ : syracuseStep 2507507 = 3761261) B3761261
theorem B1671923 : Blo 1670035 1671923 := bstep (se 1 (by rfl) ⟨1253942, by rfl⟩ : syracuseStep 1671923 = 2507885) B2507885
theorem B1671939 : Blo 1670035 1671939 := bstep (se 1 (by rfl) ⟨1253954, by rfl⟩ : syracuseStep 1671939 = 2507909) B2507909
theorem B7619341 : Blo 1670035 7619341 := bstep (se 3 (by rfl) ⟨1428626, by rfl⟩ : syracuseStep 7619341 = 2857253) B2857253
theorem B3171089 : Blo 1670035 3171089 := bstep (se 2 (by rfl) ⟨1189158, by rfl⟩ : syracuseStep 3171089 = 2378317) B2378317
theorem B2507537 : Blo 1670035 2507537 := bstep (se 2 (by rfl) ⟨940326, by rfl⟩ : syracuseStep 2507537 = 1880653) B1880653
theorem B1671955 : Blo 1670035 1671955 := bstep (se 1 (by rfl) ⟨1253966, by rfl⟩ : syracuseStep 1671955 = 2507933) B2507933
theorem B2507555 : Blo 1670035 2507555 := bstep (se 1 (by rfl) ⟨1880666, by rfl⟩ : syracuseStep 2507555 = 3761333) B3761333
theorem B1671971 : Blo 1670035 1671971 := bstep (se 1 (by rfl) ⟨1253978, by rfl⟩ : syracuseStep 1671971 = 2507957) B2507957
theorem B2818867 : Blo 1670035 2818867 := bstep (se 1 (by rfl) ⟨2114150, by rfl⟩ : syracuseStep 2818867 = 4228301) B4228301
theorem B1671987 : Blo 1670035 1671987 := bstep (se 1 (by rfl) ⟨1253990, by rfl⟩ : syracuseStep 1671987 = 2507981) B2507981
theorem B2507585 : Blo 1670035 2507585 := bstep (se 2 (by rfl) ⟨940344, by rfl⟩ : syracuseStep 2507585 = 1880689) B1880689
theorem B1672003 : Blo 1670035 1672003 := bstep (se 1 (by rfl) ⟨1254002, by rfl⟩ : syracuseStep 1672003 = 2508005) B2508005
theorem B2540369 : Blo 1670035 2540369 := bstep (se 2 (by rfl) ⟨952638, by rfl⟩ : syracuseStep 2540369 = 1905277) B1905277
theorem B2507603 : Blo 1670035 2507603 := bstep (se 1 (by rfl) ⟨1880702, by rfl⟩ : syracuseStep 2507603 = 3761405) B3761405
theorem B1672019 : Blo 1670035 1672019 := bstep (se 1 (by rfl) ⟨1254014, by rfl⟩ : syracuseStep 1672019 = 2508029) B2508029
theorem B8463203 : Blo 1670035 8463203 := bstep (se 1 (by rfl) ⟨6347402, by rfl⟩ : syracuseStep 8463203 = 12694805) B12694805
theorem B1672035 : Blo 1670035 1672035 := bstep (se 1 (by rfl) ⟨1254026, by rfl⟩ : syracuseStep 1672035 = 2508053) B2508053
theorem B7136113 : Blo 1670035 7136113 := bstep (se 2 (by rfl) ⟨2676042, by rfl⟩ : syracuseStep 7136113 = 5352085) B5352085
theorem B3761009 : Blo 1670035 3761009 := bstep (se 2 (by rfl) ⟨1410378, by rfl⟩ : syracuseStep 3761009 = 2820757) B2820757
theorem B2114419 : Blo 1670035 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B2507633 : Blo 1670035 2507633 := bstep (se 2 (by rfl) ⟨940362, by rfl⟩ : syracuseStep 2507633 = 1880725) B1880725
theorem B3761027 : Blo 1670035 3761027 := bstep (se 1 (by rfl) ⟨2820770, by rfl⟩ : syracuseStep 3761027 = 5641541) B5641541
theorem B2507651 : Blo 1670035 2507651 := bstep (se 1 (by rfl) ⟨1880738, by rfl⟩ : syracuseStep 2507651 = 3761477) B3761477
theorem B5637005 : Blo 1670035 5637005 := bstep (se 3 (by rfl) ⟨1056938, by rfl⟩ : syracuseStep 5637005 = 2113877) B2113877
theorem B4760461 : Blo 1670035 4760461 := bstep (se 3 (by rfl) ⟨892586, by rfl⟩ : syracuseStep 4760461 = 1785173) B1785173
theorem B2507681 : Blo 1670035 2507681 := bstep (se 2 (by rfl) ⟨940380, by rfl⟩ : syracuseStep 2507681 = 1880761) B1880761
theorem B4015025 : Blo 1670035 4015025 := bstep (se 2 (by rfl) ⟨1505634, by rfl⟩ : syracuseStep 4015025 = 3011269) B3011269
theorem B2507699 : Blo 1670035 2507699 := bstep (se 1 (by rfl) ⟨1880774, by rfl⟩ : syracuseStep 2507699 = 3761549) B3761549
theorem B2819009 : Blo 1670035 2819009 := bstep (se 2 (by rfl) ⟨1057128, by rfl⟩ : syracuseStep 2819009 = 2114257) B2114257
theorem B5637059 : Blo 1670035 5637059 := bstep (se 1 (by rfl) ⟨4227794, by rfl⟩ : syracuseStep 5637059 = 8455589) B8455589
theorem B2507729 : Blo 1670035 2507729 := bstep (se 2 (by rfl) ⟨940398, by rfl⟩ : syracuseStep 2507729 = 1880797) B1880797
theorem B2114515 : Blo 1670035 2114515 := bstep (se 1 (by rfl) ⟨1585886, by rfl⟩ : syracuseStep 2114515 = 3171773) B3171773
theorem B2507747 : Blo 1670035 2507747 := bstep (se 1 (by rfl) ⟨1880810, by rfl⟩ : syracuseStep 2507747 = 3761621) B3761621
theorem B2507777 : Blo 1670035 2507777 := bstep (se 2 (by rfl) ⟨940416, by rfl⟩ : syracuseStep 2507777 = 1880833) B1880833
theorem B2507795 : Blo 1670035 2507795 := bstep (se 1 (by rfl) ⟨1880846, by rfl⟩ : syracuseStep 2507795 = 3761693) B3761693
theorem B10159139 : Blo 1670035 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B6865955 : Blo 1670035 6865955 := bstep (se 1 (by rfl) ⟨5149466, by rfl⟩ : syracuseStep 6865955 = 10298933) B10298933
theorem B2008099 : Blo 1670035 2008099 := bstep (se 1 (by rfl) ⟨1506074, by rfl⟩ : syracuseStep 2008099 = 3012149) B3012149
theorem B5350445 : Blo 1670035 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B2507825 : Blo 1670035 2507825 := bstep (se 2 (by rfl) ⟨940434, by rfl⟩ : syracuseStep 2507825 = 1880869) B1880869
theorem B2819137 : Blo 1670035 2819137 := bstep (se 2 (by rfl) ⟨1057176, by rfl⟩ : syracuseStep 2819137 = 2114353) B2114353
theorem B2507843 : Blo 1670035 2507843 := bstep (se 1 (by rfl) ⟨1880882, by rfl⟩ : syracuseStep 2507843 = 3761765) B3761765
theorem B2507873 : Blo 1670035 2507873 := bstep (se 2 (by rfl) ⟨940452, by rfl⟩ : syracuseStep 2507873 = 1880905) B1880905
theorem B2819171 : Blo 1670035 2819171 := bstep (se 1 (by rfl) ⟨2114378, by rfl⟩ : syracuseStep 2819171 = 4228757) B4228757
theorem B4760689 : Blo 1670035 4760689 := bstep (se 2 (by rfl) ⟨1785258, by rfl⟩ : syracuseStep 4760689 = 3570517) B3570517
theorem B2507891 : Blo 1670035 2507891 := bstep (se 1 (by rfl) ⟨1880918, by rfl⟩ : syracuseStep 2507891 = 3761837) B3761837
theorem B3761297 : Blo 1670035 3761297 := bstep (se 2 (by rfl) ⟨1410486, by rfl⟩ : syracuseStep 3761297 = 2820973) B2820973
theorem B2507921 : Blo 1670035 2507921 := bstep (se 2 (by rfl) ⟨940470, by rfl⟩ : syracuseStep 2507921 = 1880941) B1880941
theorem B3761315 : Blo 1670035 3761315 := bstep (se 1 (by rfl) ⟨2820986, by rfl⟩ : syracuseStep 3761315 = 5641973) B5641973
theorem B2507939 : Blo 1670035 2507939 := bstep (se 1 (by rfl) ⟨1880954, by rfl⟩ : syracuseStep 2507939 = 3761909) B3761909
theorem B10708145 : Blo 1670035 10708145 := bstep (se 2 (by rfl) ⟨4015554, by rfl⟩ : syracuseStep 10708145 = 8031109) B8031109
theorem B2008243 : Blo 1670035 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B2507969 : Blo 1670035 2507969 := bstep (se 2 (by rfl) ⟨940488, by rfl⟩ : syracuseStep 2507969 = 1880977) B1880977
theorem B5637329 : Blo 1670035 5637329 := bstep (se 2 (by rfl) ⟨2113998, by rfl⟩ : syracuseStep 5637329 = 4227997) B4227997
theorem B2507987 : Blo 1670035 2507987 := bstep (se 1 (by rfl) ⟨1880990, by rfl⟩ : syracuseStep 2507987 = 3761981) B3761981
theorem B2819299 : Blo 1670035 2819299 := bstep (se 1 (by rfl) ⟨2114474, by rfl⟩ : syracuseStep 2819299 = 4228949) B4228949
theorem B2508017 : Blo 1670035 2508017 := bstep (se 2 (by rfl) ⟨940506, by rfl⟩ : syracuseStep 2508017 = 1881013) B1881013
theorem B2508035 : Blo 1670035 2508035 := bstep (se 1 (by rfl) ⟨1881026, by rfl⟩ : syracuseStep 2508035 = 3762053) B3762053
theorem B4760849 : Blo 1670035 4760849 := bstep (se 2 (by rfl) ⟨1785318, by rfl⟩ : syracuseStep 4760849 = 3570637) B3570637
theorem B4228433 : Blo 1670035 4228433 := bstep (se 2 (by rfl) ⟨1585662, by rfl⟩ : syracuseStep 4228433 = 3171325) B3171325
theorem B13731185 : Blo 1670035 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B2819441 : Blo 1670035 2819441 := bstep (se 2 (by rfl) ⟨1057290, by rfl⟩ : syracuseStep 2819441 = 2114581) B2114581
theorem B4228483 : Blo 1670035 4228483 := bstep (se 1 (by rfl) ⟨3171362, by rfl⟩ : syracuseStep 4228483 = 6342725) B6342725
theorem B4760963 : Blo 1670035 4760963 := bstep (se 1 (by rfl) ⟨3570722, by rfl⟩ : syracuseStep 4760963 = 7141445) B7141445
theorem B20325773 : Blo 1670035 20325773 := bstep (se 3 (by rfl) ⟨3811082, by rfl⟩ : syracuseStep 20325773 = 7622165) B7622165
theorem B3570979 : Blo 1670035 3570979 := bstep (se 1 (by rfl) ⟨2678234, by rfl⟩ : syracuseStep 3570979 = 5356469) B5356469
theorem B2712995 : Blo 1670035 2712995 := bstep (se 1 (by rfl) ⟨2034746, by rfl⟩ : syracuseStep 2712995 = 4069493) B4069493
theorem B5293475 : Blo 1670035 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B3810737 : Blo 1670035 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B3761585 : Blo 1670035 3761585 := bstep (se 2 (by rfl) ⟨1410594, by rfl⟩ : syracuseStep 3761585 = 2821189) B2821189
theorem B2115011 : Blo 1670035 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B3761603 : Blo 1670035 3761603 := bstep (se 1 (by rfl) ⟨2821202, by rfl⟩ : syracuseStep 3761603 = 5642405) B5642405
theorem B3171811 : Blo 1670035 3171811 := bstep (se 1 (by rfl) ⟨2378858, by rfl⟩ : syracuseStep 3171811 = 4757717) B4757717
theorem B2819569 : Blo 1670035 2819569 := bstep (se 2 (by rfl) ⟨1057338, by rfl⟩ : syracuseStep 2819569 = 2114677) B2114677
theorem B4228625 : Blo 1670035 4228625 := bstep (se 2 (by rfl) ⟨1585734, by rfl⟩ : syracuseStep 4228625 = 3171469) B3171469
theorem B2819603 : Blo 1670035 2819603 := bstep (se 1 (by rfl) ⟨2114702, by rfl⟩ : syracuseStep 2819603 = 4229405) B4229405
theorem B8464013 : Blo 1670035 8464013 := bstep (se 3 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 8464013 = 3174005) B3174005
theorem B2819731 : Blo 1670035 2819731 := bstep (se 1 (by rfl) ⟨2114798, by rfl⟩ : syracuseStep 2819731 = 4229597) B4229597
theorem B3761873 : Blo 1670035 3761873 := bstep (se 2 (by rfl) ⟨1410702, by rfl⟩ : syracuseStep 3761873 = 2821405) B2821405
theorem B3761891 : Blo 1670035 3761891 := bstep (se 1 (by rfl) ⟨2821418, by rfl⟩ : syracuseStep 3761891 = 5642837) B5642837
theorem B5637869 : Blo 1670035 5637869 := bstep (se 3 (by rfl) ⟨1057100, by rfl⟩ : syracuseStep 5637869 = 2114201) B2114201
theorem B9520901 : Blo 1670035 9520901 := bstep (se 4 (by rfl) ⟨892584, by rfl⟩ : syracuseStep 9520901 = 1785169) B1785169
theorem B2819873 : Blo 1670035 2819873 := bstep (se 2 (by rfl) ⟨1057452, by rfl⟩ : syracuseStep 2819873 = 2114905) B2114905
theorem B5637923 : Blo 1670035 5637923 := bstep (se 1 (by rfl) ⟨4228442, by rfl⟩ : syracuseStep 5637923 = 8456885) B8456885
theorem B4638509 : Blo 1670035 4638509 := bstep (se 3 (by rfl) ⟨869720, by rfl⟩ : syracuseStep 4638509 = 1739441) B1739441
theorem B36151829 : Blo 1670035 36151829 := bstep (se 6 (by rfl) ⟨847308, by rfl⟩ : syracuseStep 36151829 = 1694617) B1694617
theorem B2820001 : Blo 1670035 2820001 := bstep (se 2 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 2820001 = 2115001) B2115001
theorem B3172259 : Blo 1670035 3172259 := bstep (se 1 (by rfl) ⟨2379194, by rfl⟩ : syracuseStep 3172259 = 4758389) B4758389
theorem B2820035 : Blo 1670035 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B15239153 : Blo 1670035 15239153 := bstep (se 2 (by rfl) ⟨5714682, by rfl⟩ : syracuseStep 15239153 = 11429365) B11429365
theorem B5638193 : Blo 1670035 5638193 := bstep (se 2 (by rfl) ⟨2114322, by rfl⟩ : syracuseStep 5638193 = 4228645) B4228645
theorem B2820163 : Blo 1670035 2820163 := bstep (se 1 (by rfl) ⟨2115122, by rfl⟩ : syracuseStep 2820163 = 4230245) B4230245
theorem B2115715 : Blo 1670035 2115715 := bstep (se 1 (by rfl) ⟨1586786, by rfl⟩ : syracuseStep 2115715 = 3173573) B3173573
theorem B2377873 : Blo 1670035 2377873 := bstep (se 2 (by rfl) ⟨891702, by rfl⟩ : syracuseStep 2377873 = 1783405) B1783405
theorem B2541731 : Blo 1670035 2541731 := bstep (se 1 (by rfl) ⟨1906298, by rfl⟩ : syracuseStep 2541731 = 3812597) B3812597
theorem B3172547 : Blo 1670035 3172547 := bstep (se 1 (by rfl) ⟨2379410, by rfl⟩ : syracuseStep 3172547 = 4758821) B4758821
theorem B2820305 : Blo 1670035 2820305 := bstep (se 2 (by rfl) ⟨1057614, by rfl⟩ : syracuseStep 2820305 = 2115229) B2115229
theorem B2115811 : Blo 1670035 2115811 := bstep (se 1 (by rfl) ⟨1586858, by rfl⟩ : syracuseStep 2115811 = 3173717) B3173717
theorem B9029873 : Blo 1670035 9029873 := bstep (se 2 (by rfl) ⟨3386202, by rfl⟩ : syracuseStep 9029873 = 6772405) B6772405
theorem B2820433 : Blo 1670035 2820433 := bstep (se 2 (by rfl) ⟨1057662, by rfl⟩ : syracuseStep 2820433 = 2115325) B2115325
theorem B9030001 : Blo 1670035 9030001 := bstep (se 2 (by rfl) ⟨3386250, by rfl⟩ : syracuseStep 9030001 = 6772501) B6772501
theorem B8456561 : Blo 1670035 8456561 := bstep (se 2 (by rfl) ⟨3171210, by rfl⟩ : syracuseStep 8456561 = 6342421) B6342421
theorem B2820467 : Blo 1670035 2820467 := bstep (se 1 (by rfl) ⟨2115350, by rfl⟩ : syracuseStep 2820467 = 4230701) B4230701
theorem B10701197 : Blo 1670035 10701197 := bstep (se 3 (by rfl) ⟨2006474, by rfl⟩ : syracuseStep 10701197 = 4012949) B4012949
theorem B4229617 : Blo 1670035 4229617 := bstep (se 2 (by rfl) ⟨1586106, by rfl⟩ : syracuseStep 4229617 = 3172213) B3172213
theorem B2820595 : Blo 1670035 2820595 := bstep (se 1 (by rfl) ⟨2115446, by rfl⟩ : syracuseStep 2820595 = 4230893) B4230893
theorem B6343181 : Blo 1670035 6343181 := bstep (se 3 (by rfl) ⟨1189346, by rfl⟩ : syracuseStep 6343181 = 2378693) B2378693
theorem B2542097 : Blo 1670035 2542097 := bstep (se 2 (by rfl) ⟨953286, by rfl⟩ : syracuseStep 2542097 = 1906573) B1906573
theorem B5638733 : Blo 1670035 5638733 := bstep (se 3 (by rfl) ⟨1057262, by rfl⟩ : syracuseStep 5638733 = 2114525) B2114525
theorem B8030819 : Blo 1670035 8030819 := bstep (se 1 (by rfl) ⟨6023114, by rfl⟩ : syracuseStep 8030819 = 12046229) B12046229
theorem B10709603 : Blo 1670035 10709603 := bstep (se 1 (by rfl) ⟨8032202, by rfl⟩ : syracuseStep 10709603 = 16064405) B16064405
theorem B2820737 : Blo 1670035 2820737 := bstep (se 2 (by rfl) ⟨1057776, by rfl⟩ : syracuseStep 2820737 = 2115553) B2115553
theorem B5638787 : Blo 1670035 5638787 := bstep (se 1 (by rfl) ⟨4229090, by rfl⟩ : syracuseStep 5638787 = 8458181) B8458181
theorem B4016785 : Blo 1670035 4016785 := bstep (se 2 (by rfl) ⟨1506294, by rfl⟩ : syracuseStep 4016785 = 3012589) B3012589
theorem B8030897 : Blo 1670035 8030897 := bstep (se 2 (by rfl) ⟨3011586, by rfl⟩ : syracuseStep 8030897 = 6023173) B6023173
theorem B2820865 : Blo 1670035 2820865 := bstep (se 2 (by rfl) ⟨1057824, by rfl⟩ : syracuseStep 2820865 = 2115649) B2115649
theorem B4229891 : Blo 1670035 4229891 := bstep (se 1 (by rfl) ⟨3172418, by rfl⟩ : syracuseStep 4229891 = 6344837) B6344837
theorem B5352227 : Blo 1670035 5352227 := bstep (se 1 (by rfl) ⟨4014170, by rfl⟩ : syracuseStep 5352227 = 8028341) B8028341
theorem B2820899 : Blo 1670035 2820899 := bstep (se 1 (by rfl) ⟨2115674, by rfl⟩ : syracuseStep 2820899 = 4231349) B4231349
theorem B1878835 : Blo 1670035 1878835 := bstep (se 1 (by rfl) ⟨1409126, by rfl⟩ : syracuseStep 1878835 = 2818253) B2818253
theorem B5639057 : Blo 1670035 5639057 := bstep (se 2 (by rfl) ⟨2114646, by rfl⟩ : syracuseStep 5639057 = 4229293) B4229293
theorem B2378659 : Blo 1670035 2378659 := bstep (se 1 (by rfl) ⟨1783994, by rfl⟩ : syracuseStep 2378659 = 3567989) B3567989
theorem B2821027 : Blo 1670035 2821027 := bstep (se 1 (by rfl) ⟨2115770, by rfl⟩ : syracuseStep 2821027 = 4231541) B4231541
theorem B1878979 : Blo 1670035 1878979 := bstep (se 1 (by rfl) ⟨1409234, by rfl⟩ : syracuseStep 1878979 = 2818469) B2818469
theorem B4230083 : Blo 1670035 4230083 := bstep (se 1 (by rfl) ⟨3172562, by rfl⟩ : syracuseStep 4230083 = 6345125) B6345125
theorem B3009539 : Blo 1670035 3009539 := bstep (se 1 (by rfl) ⟨2257154, by rfl⟩ : syracuseStep 3009539 = 4514309) B4514309
theorem B2821169 : Blo 1670035 2821169 := bstep (se 2 (by rfl) ⟨1057938, by rfl⟩ : syracuseStep 2821169 = 2115877) B2115877
theorem B1879123 : Blo 1670035 1879123 := bstep (se 1 (by rfl) ⟨1409342, by rfl⟩ : syracuseStep 1879123 = 2818685) B2818685
theorem B3009649 : Blo 1670035 3009649 := bstep (se 2 (by rfl) ⟨1128618, by rfl⟩ : syracuseStep 3009649 = 2257237) B2257237
theorem B3173489 : Blo 1670035 3173489 := bstep (se 2 (by rfl) ⟨1190058, by rfl⟩ : syracuseStep 3173489 = 2380117) B2380117
theorem B2821297 : Blo 1670035 2821297 := bstep (se 2 (by rfl) ⟨1057986, by rfl⟩ : syracuseStep 2821297 = 2115973) B2115973
theorem B2821331 : Blo 1670035 2821331 := bstep (se 1 (by rfl) ⟨2115998, by rfl⟩ : syracuseStep 2821331 = 4231997) B4231997
theorem B1879267 : Blo 1670035 1879267 := bstep (se 1 (by rfl) ⟨1409450, by rfl⟩ : syracuseStep 1879267 = 2818901) B2818901
theorem B3566929 : Blo 1670035 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B2821459 : Blo 1670035 2821459 := bstep (se 1 (by rfl) ⟨2116094, by rfl⟩ : syracuseStep 2821459 = 4232189) B4232189
theorem B4287857 : Blo 1670035 4287857 := bstep (se 2 (by rfl) ⟨1607946, by rfl⟩ : syracuseStep 4287857 = 3215893) B3215893
theorem B1879411 : Blo 1670035 1879411 := bstep (se 1 (by rfl) ⟨1409558, by rfl⟩ : syracuseStep 1879411 = 2819117) B2819117
theorem B2379137 : Blo 1670035 2379137 := bstep (se 2 (by rfl) ⟨892176, by rfl⟩ : syracuseStep 2379137 = 1784353) B1784353
theorem B5639597 : Blo 1670035 5639597 := bstep (se 3 (by rfl) ⟨1057424, by rfl⟩ : syracuseStep 5639597 = 2114849) B2114849
theorem B5639651 : Blo 1670035 5639651 := bstep (se 1 (by rfl) ⟨4229738, by rfl⟩ : syracuseStep 5639651 = 8459477) B8459477
theorem B2379251 : Blo 1670035 2379251 := bstep (se 1 (by rfl) ⟨1784438, by rfl⟩ : syracuseStep 2379251 = 3568877) B3568877
theorem B1879555 : Blo 1670035 1879555 := bstep (se 1 (by rfl) ⟨1409666, by rfl⟩ : syracuseStep 1879555 = 2819333) B2819333
theorem B2379331 : Blo 1670035 2379331 := bstep (se 1 (by rfl) ⟨1784498, by rfl⟩ : syracuseStep 2379331 = 3568997) B3568997
theorem B1879699 : Blo 1670035 1879699 := bstep (se 1 (by rfl) ⟨1409774, by rfl⟩ : syracuseStep 1879699 = 2819549) B2819549
theorem B3567331 : Blo 1670035 3567331 := bstep (se 1 (by rfl) ⟨2675498, by rfl⟩ : syracuseStep 3567331 = 5350997) B5350997
theorem B5639921 : Blo 1670035 5639921 := bstep (se 2 (by rfl) ⟨2114970, by rfl⟩ : syracuseStep 5639921 = 4229941) B4229941
theorem B8367857 : Blo 1670035 8367857 := bstep (se 2 (by rfl) ⟨3137946, by rfl⟩ : syracuseStep 8367857 = 6275893) B6275893
theorem B2035459 : Blo 1670035 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B8458019 : Blo 1670035 8458019 := bstep (se 1 (by rfl) ⟨6343514, by rfl⟩ : syracuseStep 8458019 = 12687029) B12687029
theorem B1879843 : Blo 1670035 1879843 := bstep (se 1 (by rfl) ⟨1409882, by rfl⟩ : syracuseStep 1879843 = 2819765) B2819765
theorem B3387217 : Blo 1670035 3387217 := bstep (se 2 (by rfl) ⟨1270206, by rfl⟩ : syracuseStep 3387217 = 2540413) B2540413
theorem B12693347 : Blo 1670035 12693347 := bstep (se 1 (by rfl) ⟨9520010, by rfl⟩ : syracuseStep 12693347 = 19040021) B19040021
theorem B4231025 : Blo 1670035 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B97677197 : Blo 1670035 97677197 := bstep (se 3 (by rfl) ⟨18314474, by rfl⟩ : syracuseStep 97677197 = 36628949) B36628949
theorem B4231075 : Blo 1670035 4231075 := bstep (se 1 (by rfl) ⟨3173306, by rfl⟩ : syracuseStep 4231075 = 6346613) B6346613
theorem B1879987 : Blo 1670035 1879987 := bstep (se 1 (by rfl) ⟨1409990, by rfl⟩ : syracuseStep 1879987 = 2819981) B2819981
theorem B1904675 : Blo 1670035 1904675 := bstep (se 1 (by rfl) ⟨1428506, by rfl⟩ : syracuseStep 1904675 = 2857013) B2857013
theorem B4231217 : Blo 1670035 4231217 := bstep (se 2 (by rfl) ⟨1586706, by rfl⟩ : syracuseStep 4231217 = 3173413) B3173413
theorem B1880131 : Blo 1670035 1880131 := bstep (se 1 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 1880131 = 2820197) B2820197
theorem B5713997 : Blo 1670035 5713997 := bstep (se 3 (by rfl) ⟨1071374, by rfl⟩ : syracuseStep 5713997 = 2142749) B2142749
theorem B5353571 : Blo 1670035 5353571 := bstep (se 1 (by rfl) ⟨4015178, by rfl⟩ : syracuseStep 5353571 = 8030357) B8030357
theorem B2379889 : Blo 1670035 2379889 := bstep (se 2 (by rfl) ⟨892458, by rfl⟩ : syracuseStep 2379889 = 1784917) B1784917
theorem B10858637 : Blo 1670035 10858637 := bstep (se 3 (by rfl) ⟨2035994, by rfl⟩ : syracuseStep 10858637 = 4071989) B4071989
theorem B11432099 : Blo 1670035 11432099 := bstep (se 1 (by rfl) ⟨8574074, by rfl⟩ : syracuseStep 11432099 = 17148149) B17148149
theorem B21418181 : Blo 1670035 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B5025997 : Blo 1670035 5025997 := bstep (se 3 (by rfl) ⟨942374, by rfl⟩ : syracuseStep 5025997 = 1884749) B1884749
theorem B6025421 : Blo 1670035 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B1880275 : Blo 1670035 1880275 := bstep (se 1 (by rfl) ⟨1410206, by rfl⟩ : syracuseStep 1880275 = 2820413) B2820413
theorem B12865763 : Blo 1670035 12865763 := bstep (se 1 (by rfl) ⟨9649322, by rfl⟩ : syracuseStep 12865763 = 19298645) B19298645
theorem B5714189 : Blo 1670035 5714189 := bstep (se 3 (by rfl) ⟨1071410, by rfl⟩ : syracuseStep 5714189 = 2142821) B2142821
theorem B5640461 : Blo 1670035 5640461 := bstep (se 3 (by rfl) ⟨1057586, by rfl⟩ : syracuseStep 5640461 = 2115173) B2115173
theorem B3010865 : Blo 1670035 3010865 := bstep (se 2 (by rfl) ⟨1129074, by rfl⟩ : syracuseStep 3010865 = 2258149) B2258149
theorem B5640515 : Blo 1670035 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B1880419 : Blo 1670035 1880419 := bstep (se 1 (by rfl) ⟨1410314, by rfl⟩ : syracuseStep 1880419 = 2820629) B2820629
theorem B22868365 : Blo 1670035 22868365 := bstep (se 3 (by rfl) ⟨4287818, by rfl⟩ : syracuseStep 22868365 = 8575637) B8575637
theorem B1880563 : Blo 1670035 1880563 := bstep (se 1 (by rfl) ⟨1410422, by rfl⟩ : syracuseStep 1880563 = 2820845) B2820845
theorem B8032817 : Blo 1670035 8032817 := bstep (se 2 (by rfl) ⟨3012306, by rfl⟩ : syracuseStep 8032817 = 6024613) B6024613
theorem B8458829 : Blo 1670035 8458829 := bstep (se 3 (by rfl) ⟨1586030, by rfl⟩ : syracuseStep 8458829 = 3172061) B3172061
theorem B5640785 : Blo 1670035 5640785 := bstep (se 2 (by rfl) ⟨2115294, by rfl⟩ : syracuseStep 5640785 = 4230589) B4230589
theorem B1880707 : Blo 1670035 1880707 := bstep (se 1 (by rfl) ⟨1410530, by rfl⟩ : syracuseStep 1880707 = 2821061) B2821061
theorem B1880851 : Blo 1670035 1880851 := bstep (se 1 (by rfl) ⟨1410638, by rfl⟩ : syracuseStep 1880851 = 2821277) B2821277
theorem B4756259 : Blo 1670035 4756259 := bstep (se 1 (by rfl) ⟨3567194, by rfl⟩ : syracuseStep 4756259 = 7134389) B7134389
theorem B7140145 : Blo 1670035 7140145 := bstep (se 2 (by rfl) ⟨2677554, by rfl⟩ : syracuseStep 7140145 = 5355109) B5355109
theorem B2143027 : Blo 1670035 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B2380595 : Blo 1670035 2380595 := bstep (se 1 (by rfl) ⟨1785446, by rfl⟩ : syracuseStep 2380595 = 3570893) B3570893
theorem B3093347 : Blo 1670035 3093347 := bstep (se 1 (by rfl) ⟨2320010, by rfl⟩ : syracuseStep 3093347 = 4640021) B4640021
theorem B1880995 : Blo 1670035 1880995 := bstep (se 1 (by rfl) ⟨1410746, by rfl⟩ : syracuseStep 1880995 = 2821493) B2821493
theorem B4232209 : Blo 1670035 4232209 := bstep (se 2 (by rfl) ⟨1587078, by rfl⟩ : syracuseStep 4232209 = 3174157) B3174157
theorem B8033357 : Blo 1670035 8033357 := bstep (se 3 (by rfl) ⟨1506254, by rfl⟩ : syracuseStep 8033357 = 3012509) B3012509
theorem B4756589 : Blo 1670035 4756589 := bstep (se 3 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 4756589 = 1783721) B1783721
theorem B5641325 : Blo 1670035 5641325 := bstep (se 3 (by rfl) ⟨1057748, by rfl⟩ : syracuseStep 5641325 = 2115497) B2115497
theorem B5641379 : Blo 1670035 5641379 := bstep (se 1 (by rfl) ⟨4231034, by rfl⟩ : syracuseStep 5641379 = 8462069) B8462069
theorem B4756657 : Blo 1670035 4756657 := bstep (se 2 (by rfl) ⟨1783746, by rfl⟩ : syracuseStep 4756657 = 3567493) B3567493
theorem B3568835 : Blo 1670035 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B10302661 : Blo 1670035 10302661 := bstep (se 4 (by rfl) ⟨965874, by rfl⟩ : syracuseStep 10302661 = 1931749) B1931749
theorem B4125905 : Blo 1670035 4125905 := bstep (se 2 (by rfl) ⟨1547214, by rfl⟩ : syracuseStep 4125905 = 3094429) B3094429
theorem B2676017 : Blo 1670035 2676017 := bstep (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) B2007013
theorem B9033029 : Blo 1670035 9033029 := bstep (se 4 (by rfl) ⟨846846, by rfl⟩ : syracuseStep 9033029 = 1693693) B1693693
theorem B2258275 : Blo 1670035 2258275 := bstep (se 1 (by rfl) ⟨1693706, by rfl⟩ : syracuseStep 2258275 = 3387413) B3387413
theorem B5084525 : Blo 1670035 5084525 := bstep (se 3 (by rfl) ⟨953348, by rfl⟩ : syracuseStep 5084525 = 1906697) B1906697
theorem B6346097 : Blo 1670035 6346097 := bstep (se 2 (by rfl) ⟨2379786, by rfl⟩ : syracuseStep 6346097 = 4759573) B4759573
theorem B5641649 : Blo 1670035 5641649 := bstep (se 2 (by rfl) ⟨2115618, by rfl⟩ : syracuseStep 5641649 = 4231237) B4231237
theorem B4756931 : Blo 1670035 4756931 := bstep (se 1 (by rfl) ⟨3567698, by rfl⟩ : syracuseStep 4756931 = 7135397) B7135397
theorem B1693219 : Blo 1670035 1693219 := bstep (se 1 (by rfl) ⟨1269914, by rfl⟩ : syracuseStep 1693219 = 2539829) B2539829
theorem B10704581 : Blo 1670035 10704581 := bstep (se 4 (by rfl) ⟨1003554, by rfl⟩ : syracuseStep 10704581 = 2007109) B2007109
theorem B3757841 : Blo 1670035 3757841 := bstep (se 2 (by rfl) ⟨1409190, by rfl⟩ : syracuseStep 3757841 = 2818381) B2818381
theorem B3757859 : Blo 1670035 3757859 := bstep (se 1 (by rfl) ⟨2818394, by rfl⟩ : syracuseStep 3757859 = 5636789) B5636789
theorem B2258723 : Blo 1670035 2258723 := bstep (se 1 (by rfl) ⟨1694042, by rfl⟩ : syracuseStep 2258723 = 3388085) B3388085
theorem B5355341 : Blo 1670035 5355341 := bstep (se 3 (by rfl) ⟨1004126, by rfl⟩ : syracuseStep 5355341 = 2008253) B2008253
theorem B5642189 : Blo 1670035 5642189 := bstep (se 3 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 5642189 = 2115821) B2115821
theorem B5642243 : Blo 1670035 5642243 := bstep (se 1 (by rfl) ⟨4231682, by rfl⟩ : syracuseStep 5642243 = 8463365) B8463365
theorem B3758129 : Blo 1670035 3758129 := bstep (se 2 (by rfl) ⟨1409298, by rfl⟩ : syracuseStep 3758129 = 2818597) B2818597
theorem B3758147 : Blo 1670035 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1783939 : Blo 1670035 1783939 := bstep (se 1 (by rfl) ⟨1337954, by rfl⟩ : syracuseStep 1783939 = 2675909) B2675909
theorem B2676883 : Blo 1670035 2676883 := bstep (se 1 (by rfl) ⟨2007662, by rfl⟩ : syracuseStep 2676883 = 4015325) B4015325
theorem B4757773 : Blo 1670035 4757773 := bstep (se 3 (by rfl) ⟨892082, by rfl⟩ : syracuseStep 4757773 = 1784165) B1784165
theorem B5642513 : Blo 1670035 5642513 := bstep (se 2 (by rfl) ⟨2115942, by rfl⟩ : syracuseStep 5642513 = 4231885) B4231885
theorem B3758417 : Blo 1670035 3758417 := bstep (se 2 (by rfl) ⟨1409406, by rfl⟩ : syracuseStep 3758417 = 2818813) B2818813
theorem B2505059 : Blo 1670035 2505059 := bstep (se 1 (by rfl) ⟨1878794, by rfl⟩ : syracuseStep 2505059 = 3757589) B3757589
theorem B3758435 : Blo 1670035 3758435 := bstep (se 1 (by rfl) ⟨2818826, by rfl⟩ : syracuseStep 3758435 = 5637653) B5637653
theorem B2505089 : Blo 1670035 2505089 := bstep (se 2 (by rfl) ⟨939408, by rfl⟩ : syracuseStep 2505089 = 1878817) B1878817
theorem B3570065 : Blo 1670035 3570065 := bstep (se 2 (by rfl) ⟨1338774, by rfl⟩ : syracuseStep 3570065 = 2677549) B2677549
theorem B2505107 : Blo 1670035 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B2677139 : Blo 1670035 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B7625123 : Blo 1670035 7625123 := bstep (se 1 (by rfl) ⟨5718842, by rfl⟩ : syracuseStep 7625123 = 11437685) B11437685
theorem B4757933 : Blo 1670035 4757933 := bstep (se 3 (by rfl) ⟨892112, by rfl⟩ : syracuseStep 4757933 = 1784225) B1784225
theorem B2505137 : Blo 1670035 2505137 := bstep (se 2 (by rfl) ⟨939426, by rfl⟩ : syracuseStep 2505137 = 1878853) B1878853
theorem B2505155 : Blo 1670035 2505155 := bstep (se 1 (by rfl) ⟨1878866, by rfl⟩ : syracuseStep 2505155 = 3757733) B3757733
theorem B2505185 : Blo 1670035 2505185 := bstep (se 2 (by rfl) ⟨939444, by rfl⟩ : syracuseStep 2505185 = 1878889) B1878889
theorem B16062947 : Blo 1670035 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B2505203 : Blo 1670035 2505203 := bstep (se 1 (by rfl) ⟨1878902, by rfl⟩ : syracuseStep 2505203 = 3757805) B3757805
theorem B2505233 : Blo 1670035 2505233 := bstep (se 2 (by rfl) ⟨939462, by rfl⟩ : syracuseStep 2505233 = 1878925) B1878925
theorem B2505251 : Blo 1670035 2505251 := bstep (se 1 (by rfl) ⟨1878938, by rfl⟩ : syracuseStep 2505251 = 3757877) B3757877
theorem B2505281 : Blo 1670035 2505281 := bstep (se 2 (by rfl) ⟨939480, by rfl⟩ : syracuseStep 2505281 = 1878961) B1878961
theorem B1784387 : Blo 1670035 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B2505299 : Blo 1670035 2505299 := bstep (se 1 (by rfl) ⟨1878974, by rfl⟩ : syracuseStep 2505299 = 3757949) B3757949
theorem B4758115 : Blo 1670035 4758115 := bstep (se 1 (by rfl) ⟨3568586, by rfl⟩ : syracuseStep 4758115 = 7137173) B7137173
theorem B2505329 : Blo 1670035 2505329 := bstep (se 2 (by rfl) ⟨939498, by rfl⟩ : syracuseStep 2505329 = 1878997) B1878997
theorem B3758705 : Blo 1670035 3758705 := bstep (se 2 (by rfl) ⟨1409514, by rfl⟩ : syracuseStep 3758705 = 2819029) B2819029
theorem B2505347 : Blo 1670035 2505347 := bstep (se 1 (by rfl) ⟨1879010, by rfl⟩ : syracuseStep 2505347 = 3758021) B3758021
theorem B3758723 : Blo 1670035 3758723 := bstep (se 1 (by rfl) ⟨2819042, by rfl⟩ : syracuseStep 3758723 = 5638085) B5638085
theorem B2505377 : Blo 1670035 2505377 := bstep (se 2 (by rfl) ⟨939516, by rfl⟩ : syracuseStep 2505377 = 1879033) B1879033
theorem B2505395 : Blo 1670035 2505395 := bstep (se 1 (by rfl) ⟨1879046, by rfl⟩ : syracuseStep 2505395 = 3758093) B3758093
theorem B2505425 : Blo 1670035 2505425 := bstep (se 2 (by rfl) ⟨939534, by rfl⟩ : syracuseStep 2505425 = 1879069) B1879069
theorem B2505443 : Blo 1670035 2505443 := bstep (se 1 (by rfl) ⟨1879082, by rfl⟩ : syracuseStep 2505443 = 3758165) B3758165
theorem B2505473 : Blo 1670035 2505473 := bstep (se 2 (by rfl) ⟨939552, by rfl⟩ : syracuseStep 2505473 = 1879105) B1879105
theorem B2505491 : Blo 1670035 2505491 := bstep (se 1 (by rfl) ⟨1879118, by rfl⟩ : syracuseStep 2505491 = 3758237) B3758237
theorem B6347555 : Blo 1670035 6347555 := bstep (se 1 (by rfl) ⟨4760666, by rfl⟩ : syracuseStep 6347555 = 9521333) B9521333
theorem B5643053 : Blo 1670035 5643053 := bstep (se 3 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 5643053 = 2116145) B2116145
theorem B2505521 : Blo 1670035 2505521 := bstep (se 2 (by rfl) ⟨939570, by rfl⟩ : syracuseStep 2505521 = 1879141) B1879141
theorem B2505539 : Blo 1670035 2505539 := bstep (se 1 (by rfl) ⟨1879154, by rfl⟩ : syracuseStep 2505539 = 3758309) B3758309
theorem B23190341 : Blo 1670035 23190341 := bstep (se 4 (by rfl) ⟨2174094, by rfl⟩ : syracuseStep 23190341 = 4348189) B4348189
theorem B2505569 : Blo 1670035 2505569 := bstep (se 2 (by rfl) ⟨939588, by rfl⟩ : syracuseStep 2505569 = 1879177) B1879177
theorem B5643107 : Blo 1670035 5643107 := bstep (se 1 (by rfl) ⟨4232330, by rfl⟩ : syracuseStep 5643107 = 8464661) B8464661
theorem B2505587 : Blo 1670035 2505587 := bstep (se 1 (by rfl) ⟨1879190, by rfl⟩ : syracuseStep 2505587 = 3758381) B3758381
theorem B2505617 : Blo 1670035 2505617 := bstep (se 2 (by rfl) ⟨939606, by rfl⟩ : syracuseStep 2505617 = 1879213) B1879213
theorem B3758993 : Blo 1670035 3758993 := bstep (se 2 (by rfl) ⟨1409622, by rfl⟩ : syracuseStep 3758993 = 2819245) B2819245
theorem B1670035 : Blo 1670035 1670035 := bstep (se 1 (by rfl) ⟨1252526, by rfl⟩ : syracuseStep 1670035 = 2505053) B2505053
theorem B1670051 : Blo 1670035 1670051 := bstep (se 1 (by rfl) ⟨1252538, by rfl⟩ : syracuseStep 1670051 = 2505077) B2505077
theorem B7134115 : Blo 1670035 7134115 := bstep (se 1 (by rfl) ⟨5350586, by rfl⟩ : syracuseStep 7134115 = 10701173) B10701173
theorem B2505635 : Blo 1670035 2505635 := bstep (se 1 (by rfl) ⟨1879226, by rfl⟩ : syracuseStep 2505635 = 3758453) B3758453
theorem B3759011 : Blo 1670035 3759011 := bstep (se 1 (by rfl) ⟨2819258, by rfl⟩ : syracuseStep 3759011 = 5638517) B5638517
theorem B1670067 : Blo 1670035 1670067 := bstep (se 1 (by rfl) ⟨1252550, by rfl⟩ : syracuseStep 1670067 = 2505101) B2505101
theorem B2505665 : Blo 1670035 2505665 := bstep (se 2 (by rfl) ⟨939624, by rfl⟩ : syracuseStep 2505665 = 1879249) B1879249
theorem B1670083 : Blo 1670035 1670083 := bstep (se 1 (by rfl) ⟨1252562, by rfl⟩ : syracuseStep 1670083 = 2505125) B2505125
theorem B4578257 : Blo 1670035 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B1670099 : Blo 1670035 1670099 := bstep (se 1 (by rfl) ⟨1252574, by rfl⟩ : syracuseStep 1670099 = 2505149) B2505149
theorem B2505683 : Blo 1670035 2505683 := bstep (se 1 (by rfl) ⟨1879262, by rfl⟩ : syracuseStep 2505683 = 3758525) B3758525
theorem B1670115 : Blo 1670035 1670115 := bstep (se 1 (by rfl) ⟨1252586, by rfl⟩ : syracuseStep 1670115 = 2505173) B2505173
theorem B4013027 : Blo 1670035 4013027 := bstep (se 1 (by rfl) ⟨3009770, by rfl⟩ : syracuseStep 4013027 = 6019541) B6019541
theorem B2505713 : Blo 1670035 2505713 := bstep (se 2 (by rfl) ⟨939642, by rfl⟩ : syracuseStep 2505713 = 1879285) B1879285
theorem B1670131 : Blo 1670035 1670131 := bstep (se 1 (by rfl) ⟨1252598, by rfl⟩ : syracuseStep 1670131 = 2505197) B2505197
theorem B1670147 : Blo 1670035 1670147 := bstep (se 1 (by rfl) ⟨1252610, by rfl⟩ : syracuseStep 1670147 = 2505221) B2505221
theorem B2505731 : Blo 1670035 2505731 := bstep (se 1 (by rfl) ⟨1879298, by rfl⟩ : syracuseStep 2505731 = 3758597) B3758597
theorem B1694723 : Blo 1670035 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B1670163 : Blo 1670035 1670163 := bstep (se 1 (by rfl) ⟨1252622, by rfl⟩ : syracuseStep 1670163 = 2505245) B2505245
theorem B2505761 : Blo 1670035 2505761 := bstep (se 2 (by rfl) ⟨939660, by rfl⟩ : syracuseStep 2505761 = 1879321) B1879321
theorem B1670179 : Blo 1670035 1670179 := bstep (se 1 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 1670179 = 2505269) B2505269
theorem B1670195 : Blo 1670035 1670195 := bstep (se 1 (by rfl) ⟨1252646, by rfl⟩ : syracuseStep 1670195 = 2505293) B2505293
theorem B2505779 : Blo 1670035 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1670211 : Blo 1670035 1670211 := bstep (se 1 (by rfl) ⟨1252658, by rfl⟩ : syracuseStep 1670211 = 2505317) B2505317
theorem B6020173 : Blo 1670035 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B2505809 : Blo 1670035 2505809 := bstep (se 2 (by rfl) ⟨939678, by rfl⟩ : syracuseStep 2505809 = 1879357) B1879357
theorem B1670227 : Blo 1670035 1670227 := bstep (se 1 (by rfl) ⟨1252670, by rfl⟩ : syracuseStep 1670227 = 2505341) B2505341
theorem B1670243 : Blo 1670035 1670243 := bstep (se 1 (by rfl) ⟨1252682, by rfl⟩ : syracuseStep 1670243 = 2505365) B2505365
theorem B2505827 : Blo 1670035 2505827 := bstep (se 1 (by rfl) ⟨1879370, by rfl⟩ : syracuseStep 2505827 = 3758741) B3758741
theorem B1670259 : Blo 1670035 1670259 := bstep (se 1 (by rfl) ⟨1252694, by rfl⟩ : syracuseStep 1670259 = 2505389) B2505389
theorem B2505857 : Blo 1670035 2505857 := bstep (se 2 (by rfl) ⟨939696, by rfl⟩ : syracuseStep 2505857 = 1879393) B1879393
theorem B1670275 : Blo 1670035 1670275 := bstep (se 1 (by rfl) ⟨1252706, by rfl⟩ : syracuseStep 1670275 = 2505413) B2505413
theorem B1670291 : Blo 1670035 1670291 := bstep (se 1 (by rfl) ⟨1252718, by rfl⟩ : syracuseStep 1670291 = 2505437) B2505437
theorem B2505875 : Blo 1670035 2505875 := bstep (se 1 (by rfl) ⟨1879406, by rfl⟩ : syracuseStep 2505875 = 3758813) B3758813
theorem B1670307 : Blo 1670035 1670307 := bstep (se 1 (by rfl) ⟨1252730, by rfl⟩ : syracuseStep 1670307 = 2505461) B2505461
theorem B2505905 : Blo 1670035 2505905 := bstep (se 2 (by rfl) ⟨939714, by rfl⟩ : syracuseStep 2505905 = 1879429) B1879429
theorem B3759281 : Blo 1670035 3759281 := bstep (se 2 (by rfl) ⟨1409730, by rfl⟩ : syracuseStep 3759281 = 2819461) B2819461
theorem B1670323 : Blo 1670035 1670323 := bstep (se 1 (by rfl) ⟨1252742, by rfl⟩ : syracuseStep 1670323 = 2505485) B2505485
theorem B1670339 : Blo 1670035 1670339 := bstep (se 1 (by rfl) ⟨1252754, by rfl⟩ : syracuseStep 1670339 = 2505509) B2505509
theorem B2505923 : Blo 1670035 2505923 := bstep (se 1 (by rfl) ⟨1879442, by rfl⟩ : syracuseStep 2505923 = 3758885) B3758885
theorem B3759299 : Blo 1670035 3759299 := bstep (se 1 (by rfl) ⟨2819474, by rfl⟩ : syracuseStep 3759299 = 5638949) B5638949
theorem B14277829 : Blo 1670035 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B1670355 : Blo 1670035 1670355 := bstep (se 1 (by rfl) ⟨1252766, by rfl⟩ : syracuseStep 1670355 = 2505533) B2505533
theorem B2505953 : Blo 1670035 2505953 := bstep (se 2 (by rfl) ⟨939732, by rfl⟩ : syracuseStep 2505953 = 1879465) B1879465
theorem B1670371 : Blo 1670035 1670371 := bstep (se 1 (by rfl) ⟨1252778, by rfl⟩ : syracuseStep 1670371 = 2505557) B2505557
theorem B1670387 : Blo 1670035 1670387 := bstep (se 1 (by rfl) ⟨1252790, by rfl⟩ : syracuseStep 1670387 = 2505581) B2505581
theorem B2505971 : Blo 1670035 2505971 := bstep (se 1 (by rfl) ⟨1879478, by rfl⟩ : syracuseStep 2505971 = 3758957) B3758957
theorem B1670403 : Blo 1670035 1670403 := bstep (se 1 (by rfl) ⟨1252802, by rfl⟩ : syracuseStep 1670403 = 2505605) B2505605
theorem B16063757 : Blo 1670035 16063757 := bstep (se 3 (by rfl) ⟨3011954, by rfl⟩ : syracuseStep 16063757 = 6023909) B6023909
theorem B2506001 : Blo 1670035 2506001 := bstep (se 2 (by rfl) ⟨939750, by rfl⟩ : syracuseStep 2506001 = 1879501) B1879501
theorem B3570961 : Blo 1670035 3570961 := bstep (se 2 (by rfl) ⟨1339110, by rfl⟩ : syracuseStep 3570961 = 2678221) B2678221
theorem B1670419 : Blo 1670035 1670419 := bstep (se 1 (by rfl) ⟨1252814, by rfl⟩ : syracuseStep 1670419 = 2505629) B2505629
theorem B1670435 : Blo 1670035 1670435 := bstep (se 1 (by rfl) ⟨1252826, by rfl⟩ : syracuseStep 1670435 = 2505653) B2505653
theorem B2506019 : Blo 1670035 2506019 := bstep (se 1 (by rfl) ⟨1879514, by rfl⟩ : syracuseStep 2506019 = 3759029) B3759029
theorem B8576291 : Blo 1670035 8576291 := bstep (se 1 (by rfl) ⟨6432218, by rfl⟩ : syracuseStep 8576291 = 12864437) B12864437
theorem B1670451 : Blo 1670035 1670451 := bstep (se 1 (by rfl) ⟨1252838, by rfl⟩ : syracuseStep 1670451 = 2505677) B2505677
theorem B2506049 : Blo 1670035 2506049 := bstep (se 2 (by rfl) ⟨939768, by rfl⟩ : syracuseStep 2506049 = 1879537) B1879537
theorem B1670467 : Blo 1670035 1670467 := bstep (se 1 (by rfl) ⟨1252850, by rfl⟩ : syracuseStep 1670467 = 2505701) B2505701
theorem B1670483 : Blo 1670035 1670483 := bstep (se 1 (by rfl) ⟨1252862, by rfl⟩ : syracuseStep 1670483 = 2505725) B2505725
theorem B2506067 : Blo 1670035 2506067 := bstep (se 1 (by rfl) ⟨1879550, by rfl⟩ : syracuseStep 2506067 = 3759101) B3759101
theorem B2678113 : Blo 1670035 2678113 := bstep (se 2 (by rfl) ⟨1004292, by rfl⟩ : syracuseStep 2678113 = 2008585) B2008585
theorem B1670499 : Blo 1670035 1670499 := bstep (se 1 (by rfl) ⟨1252874, by rfl⟩ : syracuseStep 1670499 = 2505749) B2505749
theorem B2506097 : Blo 1670035 2506097 := bstep (se 2 (by rfl) ⟨939786, by rfl⟩ : syracuseStep 2506097 = 1879573) B1879573
theorem B1670515 : Blo 1670035 1670515 := bstep (se 1 (by rfl) ⟨1252886, by rfl⟩ : syracuseStep 1670515 = 2505773) B2505773
theorem B1670531 : Blo 1670035 1670531 := bstep (se 1 (by rfl) ⟨1252898, by rfl⟩ : syracuseStep 1670531 = 2505797) B2505797
theorem B2506115 : Blo 1670035 2506115 := bstep (se 1 (by rfl) ⟨1879586, by rfl⟩ : syracuseStep 2506115 = 3759173) B3759173
theorem B1670547 : Blo 1670035 1670547 := bstep (se 1 (by rfl) ⟨1252910, by rfl⟩ : syracuseStep 1670547 = 2505821) B2505821
theorem B2506145 : Blo 1670035 2506145 := bstep (se 2 (by rfl) ⟨939804, by rfl⟩ : syracuseStep 2506145 = 1879609) B1879609
theorem B1670563 : Blo 1670035 1670563 := bstep (se 1 (by rfl) ⟨1252922, by rfl⟩ : syracuseStep 1670563 = 2505845) B2505845
theorem B8461745 : Blo 1670035 8461745 := bstep (se 2 (by rfl) ⟨3173154, by rfl⟩ : syracuseStep 8461745 = 6346309) B6346309
theorem B1670579 : Blo 1670035 1670579 := bstep (se 1 (by rfl) ⟨1252934, by rfl⟩ : syracuseStep 1670579 = 2505869) B2505869
theorem B2506163 : Blo 1670035 2506163 := bstep (se 1 (by rfl) ⟨1879622, by rfl⟩ : syracuseStep 2506163 = 3759245) B3759245
theorem B1670595 : Blo 1670035 1670595 := bstep (se 1 (by rfl) ⟨1252946, by rfl⟩ : syracuseStep 1670595 = 2505893) B2505893
theorem B2506193 : Blo 1670035 2506193 := bstep (se 2 (by rfl) ⟨939822, by rfl⟩ : syracuseStep 2506193 = 1879645) B1879645
theorem B3759569 : Blo 1670035 3759569 := bstep (se 2 (by rfl) ⟨1409838, by rfl⟩ : syracuseStep 3759569 = 2819677) B2819677
theorem B1670611 : Blo 1670035 1670611 := bstep (se 1 (by rfl) ⟨1252958, by rfl⟩ : syracuseStep 1670611 = 2505917) B2505917
theorem B1670627 : Blo 1670035 1670627 := bstep (se 1 (by rfl) ⟨1252970, by rfl⟩ : syracuseStep 1670627 = 2505941) B2505941
theorem B2506211 : Blo 1670035 2506211 := bstep (se 1 (by rfl) ⟨1879658, by rfl⟩ : syracuseStep 2506211 = 3759317) B3759317
theorem B3759587 : Blo 1670035 3759587 := bstep (se 1 (by rfl) ⟨2819690, by rfl⟩ : syracuseStep 3759587 = 5639381) B5639381
theorem B1670643 : Blo 1670035 1670643 := bstep (se 1 (by rfl) ⟨1252982, by rfl⟩ : syracuseStep 1670643 = 2505965) B2505965
theorem B2506241 : Blo 1670035 2506241 := bstep (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) B1879681
theorem B1670659 : Blo 1670035 1670659 := bstep (se 1 (by rfl) ⟨1252994, by rfl⟩ : syracuseStep 1670659 = 2505989) B2505989
theorem B1670675 : Blo 1670035 1670675 := bstep (se 1 (by rfl) ⟨1253006, by rfl⟩ : syracuseStep 1670675 = 2506013) B2506013
theorem B2506259 : Blo 1670035 2506259 := bstep (se 1 (by rfl) ⟨1879694, by rfl⟩ : syracuseStep 2506259 = 3759389) B3759389
theorem B1670691 : Blo 1670035 1670691 := bstep (se 1 (by rfl) ⟨1253018, by rfl⟩ : syracuseStep 1670691 = 2506037) B2506037
theorem B2506289 : Blo 1670035 2506289 := bstep (se 2 (by rfl) ⟨939858, by rfl⟩ : syracuseStep 2506289 = 1879717) B1879717
theorem B1670707 : Blo 1670035 1670707 := bstep (se 1 (by rfl) ⟨1253030, by rfl⟩ : syracuseStep 1670707 = 2506061) B2506061
theorem B1670723 : Blo 1670035 1670723 := bstep (se 1 (by rfl) ⟨1253042, by rfl⟩ : syracuseStep 1670723 = 2506085) B2506085
theorem B2506307 : Blo 1670035 2506307 := bstep (se 1 (by rfl) ⟨1879730, by rfl⟩ : syracuseStep 2506307 = 3759461) B3759461
theorem B1670739 : Blo 1670035 1670739 := bstep (se 1 (by rfl) ⟨1253054, by rfl⟩ : syracuseStep 1670739 = 2506109) B2506109
theorem B2506337 : Blo 1670035 2506337 := bstep (se 2 (by rfl) ⟨939876, by rfl⟩ : syracuseStep 2506337 = 1879753) B1879753
theorem B1670755 : Blo 1670035 1670755 := bstep (se 1 (by rfl) ⟨1253066, by rfl⟩ : syracuseStep 1670755 = 2506133) B2506133
theorem B9035363 : Blo 1670035 9035363 := bstep (se 1 (by rfl) ⟨6776522, by rfl⟩ : syracuseStep 9035363 = 13553045) B13553045
theorem B1670771 : Blo 1670035 1670771 := bstep (se 1 (by rfl) ⟨1253078, by rfl⟩ : syracuseStep 1670771 = 2506157) B2506157
theorem B2506355 : Blo 1670035 2506355 := bstep (se 1 (by rfl) ⟨1879766, by rfl⟩ : syracuseStep 2506355 = 3759533) B3759533
theorem B1670787 : Blo 1670035 1670787 := bstep (se 1 (by rfl) ⟨1253090, by rfl⟩ : syracuseStep 1670787 = 2506181) B2506181
theorem B2506385 : Blo 1670035 2506385 := bstep (se 2 (by rfl) ⟨939894, by rfl⟩ : syracuseStep 2506385 = 1879789) B1879789
theorem B1670803 : Blo 1670035 1670803 := bstep (se 1 (by rfl) ⟨1253102, by rfl⟩ : syracuseStep 1670803 = 2506205) B2506205
theorem B1670819 : Blo 1670035 1670819 := bstep (se 1 (by rfl) ⟨1253114, by rfl⟩ : syracuseStep 1670819 = 2506229) B2506229
theorem B2506403 : Blo 1670035 2506403 := bstep (se 1 (by rfl) ⟨1879802, by rfl⟩ : syracuseStep 2506403 = 3759605) B3759605
theorem B1670835 : Blo 1670035 1670835 := bstep (se 1 (by rfl) ⟨1253126, by rfl⟩ : syracuseStep 1670835 = 2506253) B2506253
theorem B2506433 : Blo 1670035 2506433 := bstep (se 2 (by rfl) ⟨939912, by rfl⟩ : syracuseStep 2506433 = 1879825) B1879825
theorem B1670851 : Blo 1670035 1670851 := bstep (se 1 (by rfl) ⟨1253138, by rfl⟩ : syracuseStep 1670851 = 2506277) B2506277
theorem B1670867 : Blo 1670035 1670867 := bstep (se 1 (by rfl) ⟨1253150, by rfl⟩ : syracuseStep 1670867 = 2506301) B2506301
theorem B2506451 : Blo 1670035 2506451 := bstep (se 1 (by rfl) ⟨1879838, by rfl⟩ : syracuseStep 2506451 = 3759677) B3759677
theorem B4013795 : Blo 1670035 4013795 := bstep (se 1 (by rfl) ⟨3010346, by rfl⟩ : syracuseStep 4013795 = 6020693) B6020693
theorem B1670883 : Blo 1670035 1670883 := bstep (se 1 (by rfl) ⟨1253162, by rfl⟩ : syracuseStep 1670883 = 2506325) B2506325
theorem B2506481 : Blo 1670035 2506481 := bstep (se 2 (by rfl) ⟨939930, by rfl⟩ : syracuseStep 2506481 = 1879861) B1879861
theorem B3759857 : Blo 1670035 3759857 := bstep (se 2 (by rfl) ⟨1409946, by rfl⟩ : syracuseStep 3759857 = 2819893) B2819893
theorem B1670899 : Blo 1670035 1670899 := bstep (se 1 (by rfl) ⟨1253174, by rfl⟩ : syracuseStep 1670899 = 2506349) B2506349
theorem B4579057 : Blo 1670035 4579057 := bstep (se 2 (by rfl) ⟨1717146, by rfl⟩ : syracuseStep 4579057 = 3434293) B3434293
theorem B1670915 : Blo 1670035 1670915 := bstep (se 1 (by rfl) ⟨1253186, by rfl⟩ : syracuseStep 1670915 = 2506373) B2506373
theorem B2506499 : Blo 1670035 2506499 := bstep (se 1 (by rfl) ⟨1879874, by rfl⟩ : syracuseStep 2506499 = 3759749) B3759749
theorem B3759875 : Blo 1670035 3759875 := bstep (se 1 (by rfl) ⟨2819906, by rfl⟩ : syracuseStep 3759875 = 5639813) B5639813
theorem B1670931 : Blo 1670035 1670931 := bstep (se 1 (by rfl) ⟨1253198, by rfl⟩ : syracuseStep 1670931 = 2506397) B2506397
theorem B2506529 : Blo 1670035 2506529 := bstep (se 2 (by rfl) ⟨939948, by rfl⟩ : syracuseStep 2506529 = 1879897) B1879897
theorem B1670947 : Blo 1670035 1670947 := bstep (se 1 (by rfl) ⟨1253210, by rfl⟩ : syracuseStep 1670947 = 2506421) B2506421
theorem B1670963 : Blo 1670035 1670963 := bstep (se 1 (by rfl) ⟨1253222, by rfl⟩ : syracuseStep 1670963 = 2506445) B2506445
theorem B2506547 : Blo 1670035 2506547 := bstep (se 1 (by rfl) ⟨1879910, by rfl⟩ : syracuseStep 2506547 = 3759821) B3759821
theorem B1670979 : Blo 1670035 1670979 := bstep (se 1 (by rfl) ⟨1253234, by rfl⟩ : syracuseStep 1670979 = 2506469) B2506469
theorem B9518917 : Blo 1670035 9518917 := bstep (se 4 (by rfl) ⟨892398, by rfl⟩ : syracuseStep 9518917 = 1784797) B1784797
theorem B2506577 : Blo 1670035 2506577 := bstep (se 2 (by rfl) ⟨939966, by rfl⟩ : syracuseStep 2506577 = 1879933) B1879933
theorem B1670995 : Blo 1670035 1670995 := bstep (se 1 (by rfl) ⟨1253246, by rfl⟩ : syracuseStep 1670995 = 2506493) B2506493
theorem B1671011 : Blo 1670035 1671011 := bstep (se 1 (by rfl) ⟨1253258, by rfl⟩ : syracuseStep 1671011 = 2506517) B2506517
theorem B2506595 : Blo 1670035 2506595 := bstep (se 1 (by rfl) ⟨1879946, by rfl⟩ : syracuseStep 2506595 = 3759893) B3759893
theorem B1671027 : Blo 1670035 1671027 := bstep (se 1 (by rfl) ⟨1253270, by rfl⟩ : syracuseStep 1671027 = 2506541) B2506541
theorem B2506625 : Blo 1670035 2506625 := bstep (se 2 (by rfl) ⟨939984, by rfl⟩ : syracuseStep 2506625 = 1879969) B1879969
theorem B1671043 : Blo 1670035 1671043 := bstep (se 1 (by rfl) ⟨1253282, by rfl⟩ : syracuseStep 1671043 = 2506565) B2506565
theorem B1671059 : Blo 1670035 1671059 := bstep (se 1 (by rfl) ⟨1253294, by rfl⟩ : syracuseStep 1671059 = 2506589) B2506589
theorem B2506643 : Blo 1670035 2506643 := bstep (se 1 (by rfl) ⟨1879982, by rfl⟩ : syracuseStep 2506643 = 3759965) B3759965
theorem B1671075 : Blo 1670035 1671075 := bstep (se 1 (by rfl) ⟨1253306, by rfl⟩ : syracuseStep 1671075 = 2506613) B2506613
theorem B2506673 : Blo 1670035 2506673 := bstep (se 2 (by rfl) ⟨940002, by rfl⟩ : syracuseStep 2506673 = 1880005) B1880005
theorem B1671091 : Blo 1670035 1671091 := bstep (se 1 (by rfl) ⟨1253318, by rfl⟩ : syracuseStep 1671091 = 2506637) B2506637
theorem B1671107 : Blo 1670035 1671107 := bstep (se 1 (by rfl) ⟨1253330, by rfl⟩ : syracuseStep 1671107 = 2506661) B2506661
theorem B2506691 : Blo 1670035 2506691 := bstep (se 1 (by rfl) ⟨1880018, by rfl⟩ : syracuseStep 2506691 = 3760037) B3760037
theorem B40640453 : Blo 1670035 40640453 := bstep (se 4 (by rfl) ⟨3810042, by rfl⟩ : syracuseStep 40640453 = 7620085) B7620085
theorem B4759505 : Blo 1670035 4759505 := bstep (se 2 (by rfl) ⟨1784814, by rfl⟩ : syracuseStep 4759505 = 3569629) B3569629
theorem B1671123 : Blo 1670035 1671123 := bstep (se 1 (by rfl) ⟨1253342, by rfl⟩ : syracuseStep 1671123 = 2506685) B2506685
theorem B2506721 : Blo 1670035 2506721 := bstep (se 2 (by rfl) ⟨940020, by rfl⟩ : syracuseStep 2506721 = 1880041) B1880041
theorem B1671139 : Blo 1670035 1671139 := bstep (se 1 (by rfl) ⟨1253354, by rfl⟩ : syracuseStep 1671139 = 2506709) B2506709
theorem B1671155 : Blo 1670035 1671155 := bstep (se 1 (by rfl) ⟨1253366, by rfl⟩ : syracuseStep 1671155 = 2506733) B2506733
theorem B2506739 : Blo 1670035 2506739 := bstep (se 1 (by rfl) ⟨1880054, by rfl⟩ : syracuseStep 2506739 = 3760109) B3760109
theorem B2506763 : Blo 1670035 2506763 := bstep (se 1 (by rfl) ⟨1880072, by rfl⟩ : syracuseStep 2506763 = 3760145) B3760145
theorem B1671179 : Blo 1670035 1671179 := bstep (se 1 (by rfl) ⟨1253384, by rfl⟩ : syracuseStep 1671179 = 2506769) B2506769
theorem B2506775 : Blo 1670035 2506775 := bstep (se 1 (by rfl) ⟨1880081, by rfl⟩ : syracuseStep 2506775 = 3760163) B3760163
theorem B1671191 : Blo 1670035 1671191 := bstep (se 1 (by rfl) ⟨1253393, by rfl⟩ : syracuseStep 1671191 = 2506787) B2506787
theorem B1671211 : Blo 1670035 1671211 := bstep (se 1 (by rfl) ⟨1253408, by rfl⟩ : syracuseStep 1671211 = 2506817) B2506817
theorem B1671223 : Blo 1670035 1671223 := bstep (se 1 (by rfl) ⟨1253417, by rfl⟩ : syracuseStep 1671223 = 2506835) B2506835
theorem B1671243 : Blo 1670035 1671243 := bstep (se 1 (by rfl) ⟨1253432, by rfl⟩ : syracuseStep 1671243 = 2506865) B2506865
theorem B1671255 : Blo 1670035 1671255 := bstep (se 1 (by rfl) ⟨1253441, by rfl⟩ : syracuseStep 1671255 = 2506883) B2506883
theorem B3760217 : Blo 1670035 3760217 := bstep (se 2 (by rfl) ⟨1410081, by rfl⟩ : syracuseStep 3760217 = 2820163) B2820163
theorem B2506841 : Blo 1670035 2506841 := bstep (se 2 (by rfl) ⟨940065, by rfl⟩ : syracuseStep 2506841 = 1880131) B1880131
theorem B5079133 : Blo 1670035 5079133 := bstep (se 3 (by rfl) ⟨952337, by rfl⟩ : syracuseStep 5079133 = 1904675) B1904675
theorem B27091037 : Blo 1670035 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B1671275 : Blo 1670035 1671275 := bstep (se 1 (by rfl) ⟨1253456, by rfl⟩ : syracuseStep 1671275 = 2506913) B2506913
theorem B1671287 : Blo 1670035 1671287 := bstep (se 1 (by rfl) ⟨1253465, by rfl⟩ : syracuseStep 1671287 = 2506931) B2506931
theorem B24084611 : Blo 1670035 24084611 := bstep (se 1 (by rfl) ⟨18063458, by rfl⟩ : syracuseStep 24084611 = 36126917) B36126917
theorem B14278787 : Blo 1670035 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B1671307 : Blo 1670035 1671307 := bstep (se 1 (by rfl) ⟨1253480, by rfl⟩ : syracuseStep 1671307 = 2506961) B2506961
theorem B2818199 : Blo 1670035 2818199 := bstep (se 1 (by rfl) ⟨2113649, by rfl⟩ : syracuseStep 2818199 = 4227299) B4227299
theorem B1671319 : Blo 1670035 1671319 := bstep (se 1 (by rfl) ⟨1253489, by rfl⟩ : syracuseStep 1671319 = 2506979) B2506979
theorem B8577175 : Blo 1670035 8577175 := bstep (se 1 (by rfl) ⟨6432881, by rfl⟩ : syracuseStep 8577175 = 12865763) B12865763
theorem B1671339 : Blo 1670035 1671339 := bstep (se 1 (by rfl) ⟨1253504, by rfl⟩ : syracuseStep 1671339 = 2507009) B2507009
theorem B3809459 : Blo 1670035 3809459 := bstep (se 1 (by rfl) ⟨2857094, by rfl⟩ : syracuseStep 3809459 = 5714189) B5714189
theorem B3760307 : Blo 1670035 3760307 := bstep (se 1 (by rfl) ⟨2820230, by rfl⟩ : syracuseStep 3760307 = 5640461) B5640461
theorem B1671351 : Blo 1670035 1671351 := bstep (se 1 (by rfl) ⟨1253513, by rfl⟩ : syracuseStep 1671351 = 2507027) B2507027
theorem B3170497 : Blo 1670035 3170497 := bstep (se 2 (by rfl) ⟨1188936, by rfl⟩ : syracuseStep 3170497 = 2377873) B2377873
theorem B2506955 : Blo 1670035 2506955 := bstep (se 1 (by rfl) ⟨1880216, by rfl⟩ : syracuseStep 2506955 = 3760433) B3760433
theorem B1671371 : Blo 1670035 1671371 := bstep (se 1 (by rfl) ⟨1253528, by rfl⟩ : syracuseStep 1671371 = 2507057) B2507057
theorem B15237325 : Blo 1670035 15237325 := bstep (se 3 (by rfl) ⟨2856998, by rfl⟩ : syracuseStep 15237325 = 5713997) B5713997
theorem B3760343 : Blo 1670035 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B2506967 : Blo 1670035 2506967 := bstep (se 1 (by rfl) ⟨1880225, by rfl⟩ : syracuseStep 2506967 = 3760451) B3760451
theorem B1671383 : Blo 1670035 1671383 := bstep (se 1 (by rfl) ⟨1253537, by rfl⟩ : syracuseStep 1671383 = 2507075) B2507075
theorem B1671403 : Blo 1670035 1671403 := bstep (se 1 (by rfl) ⟨1253552, by rfl⟩ : syracuseStep 1671403 = 2507105) B2507105
theorem B1671415 : Blo 1670035 1671415 := bstep (se 1 (by rfl) ⟨1253561, by rfl⟩ : syracuseStep 1671415 = 2507123) B2507123
theorem B1671435 : Blo 1670035 1671435 := bstep (se 1 (by rfl) ⟨1253576, by rfl⟩ : syracuseStep 1671435 = 2507153) B2507153
theorem B2818327 : Blo 1670035 2818327 := bstep (se 1 (by rfl) ⟨2113745, by rfl⟩ : syracuseStep 2818327 = 4227491) B4227491
theorem B1671447 : Blo 1670035 1671447 := bstep (se 1 (by rfl) ⟨1253585, by rfl⟩ : syracuseStep 1671447 = 2507171) B2507171
theorem B2507033 : Blo 1670035 2507033 := bstep (se 2 (by rfl) ⟨940137, by rfl⟩ : syracuseStep 2507033 = 1880275) B1880275
theorem B6701329 : Blo 1670035 6701329 := bstep (se 2 (by rfl) ⟨2512998, by rfl⟩ : syracuseStep 6701329 = 5025997) B5025997
theorem B1671467 : Blo 1670035 1671467 := bstep (se 1 (by rfl) ⟨1253600, by rfl⟩ : syracuseStep 1671467 = 2507201) B2507201
theorem B1671479 : Blo 1670035 1671479 := bstep (se 1 (by rfl) ⟨1253609, by rfl⟩ : syracuseStep 1671479 = 2507219) B2507219
theorem B2113867 : Blo 1670035 2113867 := bstep (se 1 (by rfl) ⟨1585400, by rfl⟩ : syracuseStep 2113867 = 3170801) B3170801
theorem B1671499 : Blo 1670035 1671499 := bstep (se 1 (by rfl) ⟨1253624, by rfl⟩ : syracuseStep 1671499 = 2507249) B2507249
theorem B1671511 : Blo 1670035 1671511 := bstep (se 1 (by rfl) ⟨1253633, by rfl⟩ : syracuseStep 1671511 = 2507267) B2507267
theorem B24101219 : Blo 1670035 24101219 := bstep (se 1 (by rfl) ⟨18075914, by rfl⟩ : syracuseStep 24101219 = 36151829) B36151829
theorem B1671531 : Blo 1670035 1671531 := bstep (se 1 (by rfl) ⟨1253648, by rfl⟩ : syracuseStep 1671531 = 2507297) B2507297
theorem B1671543 : Blo 1670035 1671543 := bstep (se 1 (by rfl) ⟨1253657, by rfl⟩ : syracuseStep 1671543 = 2507315) B2507315
theorem B3760523 : Blo 1670035 3760523 := bstep (se 1 (by rfl) ⟨2820392, by rfl⟩ : syracuseStep 3760523 = 5640785) B5640785
theorem B2507147 : Blo 1670035 2507147 := bstep (se 1 (by rfl) ⟨1880360, by rfl⟩ : syracuseStep 2507147 = 3760721) B3760721
theorem B1671563 : Blo 1670035 1671563 := bstep (se 1 (by rfl) ⟨1253672, by rfl⟩ : syracuseStep 1671563 = 2507345) B2507345
theorem B2507159 : Blo 1670035 2507159 := bstep (se 1 (by rfl) ⟨1880369, by rfl⟩ : syracuseStep 2507159 = 3760739) B3760739
theorem B1671575 : Blo 1670035 1671575 := bstep (se 1 (by rfl) ⟨1253681, by rfl⟩ : syracuseStep 1671575 = 2507363) B2507363
theorem B1671595 : Blo 1670035 1671595 := bstep (se 1 (by rfl) ⟨1253696, by rfl⟩ : syracuseStep 1671595 = 2507393) B2507393
theorem B1671607 : Blo 1670035 1671607 := bstep (se 1 (by rfl) ⟨1253705, by rfl⟩ : syracuseStep 1671607 = 2507411) B2507411
theorem B3760577 : Blo 1670035 3760577 := bstep (se 2 (by rfl) ⟨1410216, by rfl⟩ : syracuseStep 3760577 = 2820433) B2820433
theorem B1671627 : Blo 1670035 1671627 := bstep (se 1 (by rfl) ⟨1253720, by rfl⟩ : syracuseStep 1671627 = 2507441) B2507441
theorem B1671639 : Blo 1670035 1671639 := bstep (se 1 (by rfl) ⟨1253729, by rfl⟩ : syracuseStep 1671639 = 2507459) B2507459
theorem B8454617 : Blo 1670035 8454617 := bstep (se 2 (by rfl) ⟨3170481, by rfl⟩ : syracuseStep 8454617 = 6340963) B6340963
theorem B2507225 : Blo 1670035 2507225 := bstep (se 2 (by rfl) ⟨940209, by rfl⟩ : syracuseStep 2507225 = 1880419) B1880419
theorem B5636573 : Blo 1670035 5636573 := bstep (se 3 (by rfl) ⟨1056857, by rfl⟩ : syracuseStep 5636573 = 2113715) B2113715
theorem B1671659 : Blo 1670035 1671659 := bstep (se 1 (by rfl) ⟨1253744, by rfl⟩ : syracuseStep 1671659 = 2507489) B2507489
theorem B1671671 : Blo 1670035 1671671 := bstep (se 1 (by rfl) ⟨1253753, by rfl⟩ : syracuseStep 1671671 = 2507507) B2507507
theorem B1671691 : Blo 1670035 1671691 := bstep (se 1 (by rfl) ⟨1253768, by rfl⟩ : syracuseStep 1671691 = 2507537) B2507537
theorem B30491153 : Blo 1670035 30491153 := bstep (se 2 (by rfl) ⟨11434182, by rfl⟩ : syracuseStep 30491153 = 22868365) B22868365
theorem B3170839 : Blo 1670035 3170839 := bstep (se 1 (by rfl) ⟨2378129, by rfl⟩ : syracuseStep 3170839 = 4756259) B4756259
theorem B1671703 : Blo 1670035 1671703 := bstep (se 1 (by rfl) ⟨1253777, by rfl⟩ : syracuseStep 1671703 = 2507555) B2507555
theorem B1671723 : Blo 1670035 1671723 := bstep (se 1 (by rfl) ⟨1253792, by rfl⟩ : syracuseStep 1671723 = 2507585) B2507585
theorem B1671735 : Blo 1670035 1671735 := bstep (se 1 (by rfl) ⟨1253801, by rfl⟩ : syracuseStep 1671735 = 2507603) B2507603
theorem B2507339 : Blo 1670035 2507339 := bstep (se 1 (by rfl) ⟨1880504, by rfl⟩ : syracuseStep 2507339 = 3761009) B3761009
theorem B1671755 : Blo 1670035 1671755 := bstep (se 1 (by rfl) ⟨1253816, by rfl⟩ : syracuseStep 1671755 = 2507633) B2507633
theorem B2507351 : Blo 1670035 2507351 := bstep (se 1 (by rfl) ⟨1880513, by rfl⟩ : syracuseStep 2507351 = 3761027) B3761027
theorem B4227673 : Blo 1670035 4227673 := bstep (se 2 (by rfl) ⟨1585377, by rfl⟩ : syracuseStep 4227673 = 3170755) B3170755
theorem B1671767 : Blo 1670035 1671767 := bstep (se 1 (by rfl) ⟨1253825, by rfl⟩ : syracuseStep 1671767 = 2507651) B2507651
theorem B1671787 : Blo 1670035 1671787 := bstep (se 1 (by rfl) ⟨1253840, by rfl⟩ : syracuseStep 1671787 = 2507681) B2507681
theorem B1671799 : Blo 1670035 1671799 := bstep (se 1 (by rfl) ⟨1253849, by rfl⟩ : syracuseStep 1671799 = 2507699) B2507699
theorem B1671819 : Blo 1670035 1671819 := bstep (se 1 (by rfl) ⟨1253864, by rfl⟩ : syracuseStep 1671819 = 2507729) B2507729
theorem B1671831 : Blo 1670035 1671831 := bstep (se 1 (by rfl) ⟨1253873, by rfl⟩ : syracuseStep 1671831 = 2507747) B2507747
theorem B3760793 : Blo 1670035 3760793 := bstep (se 2 (by rfl) ⟨1410297, by rfl⟩ : syracuseStep 3760793 = 2820595) B2820595
theorem B2507417 : Blo 1670035 2507417 := bstep (se 2 (by rfl) ⟨940281, by rfl⟩ : syracuseStep 2507417 = 1880563) B1880563
theorem B1671851 : Blo 1670035 1671851 := bstep (se 1 (by rfl) ⟨1253888, by rfl⟩ : syracuseStep 1671851 = 2507777) B2507777
theorem B1671863 : Blo 1670035 1671863 := bstep (se 1 (by rfl) ⟨1253897, by rfl⟩ : syracuseStep 1671863 = 2507795) B2507795
theorem B1671883 : Blo 1670035 1671883 := bstep (se 1 (by rfl) ⟨1253912, by rfl⟩ : syracuseStep 1671883 = 2507825) B2507825
theorem B1671895 : Blo 1670035 1671895 := bstep (se 1 (by rfl) ⟨1253921, by rfl⟩ : syracuseStep 1671895 = 2507843) B2507843
theorem B1671915 : Blo 1670035 1671915 := bstep (se 1 (by rfl) ⟨1253936, by rfl⟩ : syracuseStep 1671915 = 2507873) B2507873
theorem B3171059 : Blo 1670035 3171059 := bstep (se 1 (by rfl) ⟨2378294, by rfl⟩ : syracuseStep 3171059 = 4756589) B4756589
theorem B3760883 : Blo 1670035 3760883 := bstep (se 1 (by rfl) ⟨2820662, by rfl⟩ : syracuseStep 3760883 = 5641325) B5641325
theorem B1671927 : Blo 1670035 1671927 := bstep (se 1 (by rfl) ⟨1253945, by rfl⟩ : syracuseStep 1671927 = 2507891) B2507891
theorem B2507531 : Blo 1670035 2507531 := bstep (se 1 (by rfl) ⟨1880648, by rfl⟩ : syracuseStep 2507531 = 3761297) B3761297
theorem B1671947 : Blo 1670035 1671947 := bstep (se 1 (by rfl) ⟨1253960, by rfl⟩ : syracuseStep 1671947 = 2507921) B2507921
theorem B3760919 : Blo 1670035 3760919 := bstep (se 1 (by rfl) ⟨2820689, by rfl⟩ : syracuseStep 3760919 = 5641379) B5641379
theorem B2507543 : Blo 1670035 2507543 := bstep (se 1 (by rfl) ⟨1880657, by rfl⟩ : syracuseStep 2507543 = 3761315) B3761315
theorem B1671959 : Blo 1670035 1671959 := bstep (se 1 (by rfl) ⟨1253969, by rfl⟩ : syracuseStep 1671959 = 2507939) B2507939
theorem B1671979 : Blo 1670035 1671979 := bstep (se 1 (by rfl) ⟨1253984, by rfl⟩ : syracuseStep 1671979 = 2507969) B2507969
theorem B7136045 : Blo 1670035 7136045 := bstep (se 3 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 7136045 = 2676017) B2676017
theorem B8028973 : Blo 1670035 8028973 := bstep (se 3 (by rfl) ⟨1505432, by rfl⟩ : syracuseStep 8028973 = 3010865) B3010865
theorem B1671991 : Blo 1670035 1671991 := bstep (se 1 (by rfl) ⟨1253993, by rfl⟩ : syracuseStep 1671991 = 2507987) B2507987
theorem B1672011 : Blo 1670035 1672011 := bstep (se 1 (by rfl) ⟨1254008, by rfl⟩ : syracuseStep 1672011 = 2508017) B2508017
theorem B1672023 : Blo 1670035 1672023 := bstep (se 1 (by rfl) ⟨1254017, by rfl⟩ : syracuseStep 1672023 = 2508035) B2508035
theorem B2507609 : Blo 1670035 2507609 := bstep (se 2 (by rfl) ⟨940353, by rfl⟩ : syracuseStep 2507609 = 1880707) B1880707
theorem B6022019 : Blo 1670035 6022019 := bstep (se 1 (by rfl) ⟨4516514, by rfl⟩ : syracuseStep 6022019 = 9033029) B9033029
theorem B2818955 : Blo 1670035 2818955 := bstep (se 1 (by rfl) ⟨2114216, by rfl⟩ : syracuseStep 2818955 = 4228433) B4228433
theorem B2540491 : Blo 1670035 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B3761099 : Blo 1670035 3761099 := bstep (se 1 (by rfl) ⟨2820824, by rfl⟩ : syracuseStep 3761099 = 5641649) B5641649
theorem B2507723 : Blo 1670035 2507723 := bstep (se 1 (by rfl) ⟨1880792, by rfl⟩ : syracuseStep 2507723 = 3761585) B3761585
theorem B3171287 : Blo 1670035 3171287 := bstep (se 1 (by rfl) ⟨2378465, by rfl⟩ : syracuseStep 3171287 = 4756931) B4756931
theorem B2507735 : Blo 1670035 2507735 := bstep (se 1 (by rfl) ⟨1880801, by rfl⟩ : syracuseStep 2507735 = 3761603) B3761603
theorem B3761153 : Blo 1670035 3761153 := bstep (se 2 (by rfl) ⟨1410432, by rfl⟩ : syracuseStep 3761153 = 2820865) B2820865
theorem B2819083 : Blo 1670035 2819083 := bstep (se 1 (by rfl) ⟨2114312, by rfl⟩ : syracuseStep 2819083 = 4228625) B4228625
theorem B10159121 : Blo 1670035 10159121 := bstep (se 2 (by rfl) ⟨3809670, by rfl⟩ : syracuseStep 10159121 = 7619341) B7619341
theorem B2507801 : Blo 1670035 2507801 := bstep (se 2 (by rfl) ⟨940425, by rfl⟩ : syracuseStep 2507801 = 1880851) B1880851
theorem B9520193 : Blo 1670035 9520193 := bstep (se 2 (by rfl) ⟨3570072, by rfl⟩ : syracuseStep 9520193 = 7140145) B7140145
theorem B7136387 : Blo 1670035 7136387 := bstep (se 1 (by rfl) ⟨5352290, by rfl⟩ : syracuseStep 7136387 = 10704581) B10704581
theorem B2507915 : Blo 1670035 2507915 := bstep (se 1 (by rfl) ⟨1880936, by rfl⟩ : syracuseStep 2507915 = 3761873) B3761873
theorem B2507927 : Blo 1670035 2507927 := bstep (se 1 (by rfl) ⟨1880945, by rfl⟩ : syracuseStep 2507927 = 3761891) B3761891
theorem B2819225 : Blo 1670035 2819225 := bstep (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) B2114419
theorem B45737141 : Blo 1670035 45737141 := bstep (se 5 (by rfl) ⟨2143928, by rfl⟩ : syracuseStep 45737141 = 4287857) B4287857
theorem B9512153 : Blo 1670035 9512153 := bstep (se 2 (by rfl) ⟨3567057, by rfl⟩ : syracuseStep 9512153 = 7134115) B7134115
theorem B3171545 : Blo 1670035 3171545 := bstep (se 2 (by rfl) ⟨1189329, by rfl⟩ : syracuseStep 3171545 = 2378659) B2378659
theorem B3761369 : Blo 1670035 3761369 := bstep (se 2 (by rfl) ⟨1410513, by rfl⟩ : syracuseStep 3761369 = 2821027) B2821027
theorem B2507993 : Blo 1670035 2507993 := bstep (se 2 (by rfl) ⟨940497, by rfl⟩ : syracuseStep 2507993 = 1880995) B1880995
theorem B24421637 : Blo 1670035 24421637 := bstep (se 4 (by rfl) ⟨2289528, by rfl⟩ : syracuseStep 24421637 = 4579057) B4579057
theorem B2114839 : Blo 1670035 2114839 := bstep (se 1 (by rfl) ⟨1586129, by rfl⟩ : syracuseStep 2114839 = 3172259) B3172259
theorem B2819353 : Blo 1670035 2819353 := bstep (se 2 (by rfl) ⟨1057257, by rfl⟩ : syracuseStep 2819353 = 2114515) B2114515
theorem B3761459 : Blo 1670035 3761459 := bstep (se 1 (by rfl) ⟨2821094, by rfl⟩ : syracuseStep 3761459 = 5642189) B5642189
theorem B10159435 : Blo 1670035 10159435 := bstep (se 1 (by rfl) ⟨7619576, by rfl⟩ : syracuseStep 10159435 = 15239153) B15239153
theorem B3761495 : Blo 1670035 3761495 := bstep (se 1 (by rfl) ⟨2821121, by rfl⟩ : syracuseStep 3761495 = 5642243) B5642243
theorem B10855781 : Blo 1670035 10855781 := bstep (se 4 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 10855781 = 2035459) B2035459
theorem B3761675 : Blo 1670035 3761675 := bstep (se 1 (by rfl) ⟨2821256, by rfl⟩ : syracuseStep 3761675 = 5642513) B5642513
theorem B6342209 : Blo 1670035 6342209 := bstep (se 2 (by rfl) ⟨2378328, by rfl⟩ : syracuseStep 6342209 = 4756657) B4756657
theorem B3761729 : Blo 1670035 3761729 := bstep (se 2 (by rfl) ⟨1410648, by rfl⟩ : syracuseStep 3761729 = 2821297) B2821297
theorem B5637707 : Blo 1670035 5637707 := bstep (se 1 (by rfl) ⟨4228280, by rfl⟩ : syracuseStep 5637707 = 8456561) B8456561
theorem B3171955 : Blo 1670035 3171955 := bstep (se 1 (by rfl) ⟨2378966, by rfl⟩ : syracuseStep 3171955 = 4757933) B4757933
theorem B10708631 : Blo 1670035 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B4228787 : Blo 1670035 4228787 := bstep (se 1 (by rfl) ⟨3171590, by rfl⟩ : syracuseStep 4228787 = 6343181) B6343181
theorem B4761281 : Blo 1670035 4761281 := bstep (se 2 (by rfl) ⟨1785480, by rfl⟩ : syracuseStep 4761281 = 3570961) B3570961
theorem B4761305 : Blo 1670035 4761305 := bstep (se 2 (by rfl) ⟨1785489, by rfl⟩ : syracuseStep 4761305 = 3570979) B3570979
theorem B3761945 : Blo 1670035 3761945 := bstep (se 2 (by rfl) ⟨1410729, by rfl⟩ : syracuseStep 3761945 = 2821459) B2821459
theorem B2819927 : Blo 1670035 2819927 := bstep (se 1 (by rfl) ⟨2114945, by rfl⟩ : syracuseStep 2819927 = 4229891) B4229891
theorem B5637977 : Blo 1670035 5637977 := bstep (se 2 (by rfl) ⟨2114241, by rfl⟩ : syracuseStep 5637977 = 4228483) B4228483
theorem B3762035 : Blo 1670035 3762035 := bstep (se 1 (by rfl) ⟨2821526, by rfl⟩ : syracuseStep 3762035 = 5643053) B5643053
theorem B3762071 : Blo 1670035 3762071 := bstep (se 1 (by rfl) ⟨2821553, by rfl⟩ : syracuseStep 3762071 = 5643107) B5643107
theorem B2820055 : Blo 1670035 2820055 := bstep (se 1 (by rfl) ⟨2115041, by rfl⟩ : syracuseStep 2820055 = 4230083) B4230083
theorem B4229081 : Blo 1670035 4229081 := bstep (se 2 (by rfl) ⟨1585905, by rfl⟩ : syracuseStep 4229081 = 3171811) B3171811
theorem B8456237 : Blo 1670035 8456237 := bstep (se 3 (by rfl) ⟨1585544, by rfl⟩ : syracuseStep 8456237 = 3171089) B3171089
theorem B2115659 : Blo 1670035 2115659 := bstep (se 1 (by rfl) ⟨1586744, by rfl⟩ : syracuseStep 2115659 = 3173489) B3173489
theorem B3172441 : Blo 1670035 3172441 := bstep (se 2 (by rfl) ⟨1189665, by rfl⟩ : syracuseStep 3172441 = 2379331) B2379331
theorem B6023261 : Blo 1670035 6023261 := bstep (se 3 (by rfl) ⟨1129361, by rfl⟩ : syracuseStep 6023261 = 2258723) B2258723
theorem B10709171 : Blo 1670035 10709171 := bstep (se 1 (by rfl) ⟨8031878, by rfl⟩ : syracuseStep 10709171 = 16063757) B16063757
theorem B6023575 : Blo 1670035 6023575 := bstep (se 1 (by rfl) ⟨4517681, by rfl⟩ : syracuseStep 6023575 = 9035363) B9035363
theorem B12691889 : Blo 1670035 12691889 := bstep (se 2 (by rfl) ⟨4759458, by rfl⟩ : syracuseStep 12691889 = 9518917) B9518917
theorem B4516289 : Blo 1670035 4516289 := bstep (se 2 (by rfl) ⟨1693608, by rfl⟩ : syracuseStep 4516289 = 3387217) B3387217
theorem B5638679 : Blo 1670035 5638679 := bstep (se 1 (by rfl) ⟨4229009, by rfl⟩ : syracuseStep 5638679 = 8458019) B8458019
theorem B2820683 : Blo 1670035 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B27093635 : Blo 1670035 27093635 := bstep (se 1 (by rfl) ⟨20320226, by rfl⟩ : syracuseStep 27093635 = 40640453) B40640453
theorem B3173003 : Blo 1670035 3173003 := bstep (se 1 (by rfl) ⟨2379752, by rfl⟩ : syracuseStep 3173003 = 4759505) B4759505
theorem B2820811 : Blo 1670035 2820811 := bstep (se 1 (by rfl) ⟨2115608, by rfl⟩ : syracuseStep 2820811 = 4231217) B4231217
theorem B7621399 : Blo 1670035 7621399 := bstep (se 1 (by rfl) ⟨5716049, by rfl⟩ : syracuseStep 7621399 = 11432099) B11432099
theorem B4016947 : Blo 1670035 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B3173185 : Blo 1670035 3173185 := bstep (se 2 (by rfl) ⟨1189944, by rfl⟩ : syracuseStep 3173185 = 2379889) B2379889
theorem B1878871 : Blo 1670035 1878871 := bstep (se 1 (by rfl) ⟨1409153, by rfl⟩ : syracuseStep 1878871 = 2818307) B2818307
theorem B2378585 : Blo 1670035 2378585 := bstep (se 2 (by rfl) ⟨891969, by rfl⟩ : syracuseStep 2378585 = 1783939) B1783939
theorem B2820953 : Blo 1670035 2820953 := bstep (se 2 (by rfl) ⟨1057857, by rfl⟩ : syracuseStep 2820953 = 2115715) B2115715
theorem B12692375 : Blo 1670035 12692375 := bstep (se 1 (by rfl) ⟨9519281, by rfl⟩ : syracuseStep 12692375 = 19038563) B19038563
theorem B2821081 : Blo 1670035 2821081 := bstep (se 2 (by rfl) ⟨1057905, by rfl⟩ : syracuseStep 2821081 = 2115811) B2115811
theorem B1879051 : Blo 1670035 1879051 := bstep (se 1 (by rfl) ⟨1409288, by rfl⟩ : syracuseStep 1879051 = 2818577) B2818577
theorem B6343697 : Blo 1670035 6343697 := bstep (se 2 (by rfl) ⟨2378886, by rfl⟩ : syracuseStep 6343697 = 4757773) B4757773
theorem B5639219 : Blo 1670035 5639219 := bstep (se 1 (by rfl) ⟨4229414, by rfl⟩ : syracuseStep 5639219 = 8458829) B8458829
theorem B32107589 : Blo 1670035 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B6777949 : Blo 1670035 6777949 := bstep (se 3 (by rfl) ⟨1270865, by rfl⟩ : syracuseStep 6777949 = 2541731) B2541731
theorem B1879159 : Blo 1670035 1879159 := bstep (se 1 (by rfl) ⟨1409369, by rfl⟩ : syracuseStep 1879159 = 2818739) B2818739
theorem B1879339 : Blo 1670035 1879339 := bstep (se 1 (by rfl) ⟨1409504, by rfl⟩ : syracuseStep 1879339 = 2819009) B2819009
theorem B5639489 : Blo 1670035 5639489 := bstep (se 2 (by rfl) ⟨2114808, by rfl⟩ : syracuseStep 5639489 = 4229617) B4229617
theorem B3566963 : Blo 1670035 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B1879447 : Blo 1670035 1879447 := bstep (se 1 (by rfl) ⟨1409585, by rfl⟩ : syracuseStep 1879447 = 2819171) B2819171
theorem B7138763 : Blo 1670035 7138763 := bstep (se 1 (by rfl) ⟨5354072, by rfl⟩ : syracuseStep 7138763 = 10708145) B10708145
theorem B2379223 : Blo 1670035 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B6344153 : Blo 1670035 6344153 := bstep (se 2 (by rfl) ⟨2379057, by rfl⟩ : syracuseStep 6344153 = 4758115) B4758115
theorem B3173899 : Blo 1670035 3173899 := bstep (se 1 (by rfl) ⟨2380424, by rfl⟩ : syracuseStep 3173899 = 4760849) B4760849
theorem B1879627 : Blo 1670035 1879627 := bstep (se 1 (by rfl) ⟨1409720, by rfl⟩ : syracuseStep 1879627 = 2819441) B2819441
theorem B4230731 : Blo 1670035 4230731 := bstep (se 1 (by rfl) ⟨3173048, by rfl⟩ : syracuseStep 4230731 = 6346097) B6346097
theorem B3173975 : Blo 1670035 3173975 := bstep (se 1 (by rfl) ⟨2380481, by rfl⟩ : syracuseStep 3173975 = 4760963) B4760963
theorem B10710629 : Blo 1670035 10710629 := bstep (se 4 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 10710629 = 2008243) B2008243
theorem B6344365 : Blo 1670035 6344365 := bstep (se 3 (by rfl) ⟨1189568, by rfl⟩ : syracuseStep 6344365 = 2379137) B2379137
theorem B1879735 : Blo 1670035 1879735 := bstep (se 1 (by rfl) ⟨1409801, by rfl⟩ : syracuseStep 1879735 = 2819603) B2819603
theorem B54202061 : Blo 1670035 54202061 := bstep (se 3 (by rfl) ⟨10162886, by rfl⟩ : syracuseStep 54202061 = 20325773) B20325773
theorem B9514817 : Blo 1670035 9514817 := bstep (se 2 (by rfl) ⟨3568056, by rfl⟩ : syracuseStep 9514817 = 7136113) B7136113
theorem B5640029 : Blo 1670035 5640029 := bstep (se 3 (by rfl) ⟨1057505, by rfl⟩ : syracuseStep 5640029 = 2115011) B2115011
theorem B1879915 : Blo 1670035 1879915 := bstep (se 1 (by rfl) ⟨1409936, by rfl⟩ : syracuseStep 1879915 = 2819873) B2819873
theorem B3092339 : Blo 1670035 3092339 := bstep (se 1 (by rfl) ⟨2319254, by rfl⟩ : syracuseStep 3092339 = 4638509) B4638509
theorem B1880023 : Blo 1670035 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B6344669 : Blo 1670035 6344669 := bstep (se 3 (by rfl) ⟨1189625, by rfl⟩ : syracuseStep 6344669 = 2379251) B2379251
theorem B1880203 : Blo 1670035 1880203 := bstep (se 1 (by rfl) ⟨1410152, by rfl⟩ : syracuseStep 1880203 = 2820305) B2820305
theorem B1880311 : Blo 1670035 1880311 := bstep (se 1 (by rfl) ⟨1410233, by rfl⟩ : syracuseStep 1880311 = 2820467) B2820467
theorem B2380043 : Blo 1670035 2380043 := bstep (se 1 (by rfl) ⟨1785032, by rfl⟩ : syracuseStep 2380043 = 3570065) B3570065
theorem B5083415 : Blo 1670035 5083415 := bstep (se 1 (by rfl) ⟨3812561, by rfl⟩ : syracuseStep 5083415 = 7625123) B7625123
theorem B5353879 : Blo 1670035 5353879 := bstep (se 1 (by rfl) ⟨4015409, by rfl⟩ : syracuseStep 5353879 = 8030819) B8030819
theorem B7139735 : Blo 1670035 7139735 := bstep (se 1 (by rfl) ⟨5354801, by rfl⟩ : syracuseStep 7139735 = 10709603) B10709603
theorem B1880491 : Blo 1670035 1880491 := bstep (se 1 (by rfl) ⟨1410368, by rfl⟩ : syracuseStep 1880491 = 2820737) B2820737
theorem B4755905 : Blo 1670035 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B5353931 : Blo 1670035 5353931 := bstep (se 1 (by rfl) ⟨4015448, by rfl⟩ : syracuseStep 5353931 = 8030897) B8030897
theorem B3011033 : Blo 1670035 3011033 := bstep (se 2 (by rfl) ⟨1129137, by rfl⟩ : syracuseStep 3011033 = 2258275) B2258275
theorem B3568151 : Blo 1670035 3568151 := bstep (se 1 (by rfl) ⟨2676113, by rfl⟩ : syracuseStep 3568151 = 5352227) B5352227
theorem B1880599 : Blo 1670035 1880599 := bstep (se 1 (by rfl) ⟨1410449, by rfl⟩ : syracuseStep 1880599 = 2820899) B2820899
theorem B4231703 : Blo 1670035 4231703 := bstep (se 1 (by rfl) ⟨3173777, by rfl⟩ : syracuseStep 4231703 = 6347555) B6347555
theorem B3052171 : Blo 1670035 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B2675351 : Blo 1670035 2675351 := bstep (se 1 (by rfl) ⟨2006513, by rfl⟩ : syracuseStep 2675351 = 4013027) B4013027
theorem B1880779 : Blo 1670035 1880779 := bstep (se 1 (by rfl) ⟨1410584, by rfl⟩ : syracuseStep 1880779 = 2821169) B2821169
theorem B2257625 : Blo 1670035 2257625 := bstep (se 2 (by rfl) ⟨846609, by rfl⟩ : syracuseStep 2257625 = 1693219) B1693219
theorem B1880887 : Blo 1670035 1880887 := bstep (se 1 (by rfl) ⟨1410665, by rfl⟩ : syracuseStep 1880887 = 2821331) B2821331
theorem B5641163 : Blo 1670035 5641163 := bstep (se 1 (by rfl) ⟨4230872, by rfl⟩ : syracuseStep 5641163 = 8461745) B8461745
theorem B4756441 : Blo 1670035 4756441 := bstep (se 2 (by rfl) ⟨1783665, by rfl⟩ : syracuseStep 4756441 = 3567331) B3567331
theorem B2675863 : Blo 1670035 2675863 := bstep (se 1 (by rfl) ⟨2006897, by rfl⟩ : syracuseStep 2675863 = 4013795) B4013795
theorem B5641433 : Blo 1670035 5641433 := bstep (se 2 (by rfl) ⟨2115537, by rfl⟩ : syracuseStep 5641433 = 4231075) B4231075
theorem B4519261 : Blo 1670035 4519261 := bstep (se 3 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 4519261 = 1694723) B1694723
theorem B7239091 : Blo 1670035 7239091 := bstep (se 1 (by rfl) ⟨5429318, by rfl⟩ : syracuseStep 7239091 = 10858637) B10858637
theorem B2676235 : Blo 1670035 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B6772241 : Blo 1670035 6772241 := bstep (se 2 (by rfl) ⟨2539590, by rfl⟩ : syracuseStep 6772241 = 5079181) B5079181
theorem B3569177 : Blo 1670035 3569177 := bstep (se 2 (by rfl) ⟨1338441, by rfl⟩ : syracuseStep 3569177 = 2676883) B2676883
theorem B3757643 : Blo 1670035 3757643 := bstep (se 1 (by rfl) ⟨2818232, by rfl⟩ : syracuseStep 3757643 = 5636465) B5636465
theorem B14276189 : Blo 1670035 14276189 := bstep (se 3 (by rfl) ⟨2676785, by rfl⟩ : syracuseStep 14276189 = 5353571) B5353571
theorem B3757697 : Blo 1670035 3757697 := bstep (se 2 (by rfl) ⟨1409136, by rfl⟩ : syracuseStep 3757697 = 2818273) B2818273
theorem B12040001 : Blo 1670035 12040001 := bstep (se 2 (by rfl) ⟨4515000, by rfl⟩ : syracuseStep 12040001 = 9030001) B9030001
theorem B3757913 : Blo 1670035 3757913 := bstep (se 2 (by rfl) ⟨1409217, by rfl⟩ : syracuseStep 3757913 = 2818435) B2818435
theorem B8460125 : Blo 1670035 8460125 := bstep (se 3 (by rfl) ⟨1586273, by rfl⟩ : syracuseStep 8460125 = 3172547) B3172547
theorem B1693579 : Blo 1670035 1693579 := bstep (se 1 (by rfl) ⟨1270184, by rfl⟩ : syracuseStep 1693579 = 2540369) B2540369
theorem B5642135 : Blo 1670035 5642135 := bstep (se 1 (by rfl) ⟨4231601, by rfl⟩ : syracuseStep 5642135 = 8463203) B8463203
theorem B3758003 : Blo 1670035 3758003 := bstep (se 1 (by rfl) ⟨2818502, by rfl⟩ : syracuseStep 3758003 = 5637005) B5637005
theorem B2676683 : Blo 1670035 2676683 := bstep (se 1 (by rfl) ⟨2007512, by rfl⟩ : syracuseStep 2676683 = 4015025) B4015025
theorem B3758039 : Blo 1670035 3758039 := bstep (se 1 (by rfl) ⟨2818529, by rfl⟩ : syracuseStep 3758039 = 5637059) B5637059
theorem B4577303 : Blo 1670035 4577303 := bstep (se 1 (by rfl) ⟨3432977, by rfl⟩ : syracuseStep 4577303 = 6865955) B6865955
theorem B5355571 : Blo 1670035 5355571 := bstep (se 1 (by rfl) ⟨4016678, by rfl⟩ : syracuseStep 5355571 = 8033357) B8033357
theorem B22870109 : Blo 1670035 22870109 := bstep (se 3 (by rfl) ⟨4288145, by rfl⟩ : syracuseStep 22870109 = 8576291) B8576291
theorem B3758219 : Blo 1670035 3758219 := bstep (se 1 (by rfl) ⟨2818664, by rfl⟩ : syracuseStep 3758219 = 5637329) B5637329
theorem B2750603 : Blo 1670035 2750603 := bstep (se 1 (by rfl) ⟨2062952, by rfl⟩ : syracuseStep 2750603 = 4125905) B4125905
theorem B3758273 : Blo 1670035 3758273 := bstep (se 2 (by rfl) ⟨1409352, by rfl⟩ : syracuseStep 3758273 = 2818705) B2818705
theorem B5355713 : Blo 1670035 5355713 := bstep (se 2 (by rfl) ⟨2008392, by rfl⟩ : syracuseStep 5355713 = 4016785) B4016785
theorem B3389683 : Blo 1670035 3389683 := bstep (se 1 (by rfl) ⟨2542262, by rfl⟩ : syracuseStep 3389683 = 5084525) B5084525
theorem B1808663 : Blo 1670035 1808663 := bstep (se 1 (by rfl) ⟨1356497, by rfl⟩ : syracuseStep 1808663 = 2712995) B2712995
theorem B3528983 : Blo 1670035 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B36616493 : Blo 1670035 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B2505113 : Blo 1670035 2505113 := bstep (se 2 (by rfl) ⟨939417, by rfl⟩ : syracuseStep 2505113 = 1878835) B1878835
theorem B3758489 : Blo 1670035 3758489 := bstep (se 2 (by rfl) ⟨1409433, by rfl⟩ : syracuseStep 3758489 = 2818867) B2818867
theorem B2857369 : Blo 1670035 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B5642675 : Blo 1670035 5642675 := bstep (se 1 (by rfl) ⟨4232006, by rfl⟩ : syracuseStep 5642675 = 8464013) B8464013
theorem B3758579 : Blo 1670035 3758579 := bstep (se 1 (by rfl) ⟨2818934, by rfl⟩ : syracuseStep 3758579 = 5637869) B5637869
theorem B6347267 : Blo 1670035 6347267 := bstep (se 1 (by rfl) ⟨4760450, by rfl⟩ : syracuseStep 6347267 = 9520901) B9520901
theorem B2505227 : Blo 1670035 2505227 := bstep (se 1 (by rfl) ⟨1878920, by rfl⟩ : syracuseStep 2505227 = 3757841) B3757841
theorem B6347281 : Blo 1670035 6347281 := bstep (se 2 (by rfl) ⟨2380230, by rfl⟩ : syracuseStep 6347281 = 4760461) B4760461
theorem B2505239 : Blo 1670035 2505239 := bstep (se 1 (by rfl) ⟨1878929, by rfl⟩ : syracuseStep 2505239 = 3757859) B3757859
theorem B3758615 : Blo 1670035 3758615 := bstep (se 1 (by rfl) ⟨2818961, by rfl⟩ : syracuseStep 3758615 = 5637923) B5637923
theorem B3570227 : Blo 1670035 3570227 := bstep (se 1 (by rfl) ⟨2677670, by rfl⟩ : syracuseStep 3570227 = 5355341) B5355341
theorem B2505305 : Blo 1670035 2505305 := bstep (se 2 (by rfl) ⟨939489, by rfl⟩ : syracuseStep 2505305 = 1878979) B1878979
theorem B5642945 : Blo 1670035 5642945 := bstep (se 2 (by rfl) ⟨2116104, by rfl⟩ : syracuseStep 5642945 = 4232209) B4232209
theorem B2505419 : Blo 1670035 2505419 := bstep (se 1 (by rfl) ⟨1879064, by rfl⟩ : syracuseStep 2505419 = 3758129) B3758129
theorem B3758795 : Blo 1670035 3758795 := bstep (se 1 (by rfl) ⟨2819096, by rfl⟩ : syracuseStep 3758795 = 5638193) B5638193
theorem B2505431 : Blo 1670035 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B2677465 : Blo 1670035 2677465 := bstep (se 2 (by rfl) ⟨1004049, by rfl⟩ : syracuseStep 2677465 = 2008099) B2008099
theorem B3758849 : Blo 1670035 3758849 := bstep (se 2 (by rfl) ⟨1409568, by rfl⟩ : syracuseStep 3758849 = 2819137) B2819137
theorem B2505497 : Blo 1670035 2505497 := bstep (se 2 (by rfl) ⟨939561, by rfl⟩ : syracuseStep 2505497 = 1879123) B1879123
theorem B21420845 : Blo 1670035 21420845 := bstep (se 3 (by rfl) ⟨4016408, by rfl⟩ : syracuseStep 21420845 = 8032817) B8032817
theorem B4012865 : Blo 1670035 4012865 := bstep (se 2 (by rfl) ⟨1504824, by rfl⟩ : syracuseStep 4012865 = 3009649) B3009649
theorem B6347585 : Blo 1670035 6347585 := bstep (se 2 (by rfl) ⟨2380344, by rfl⟩ : syracuseStep 6347585 = 4760689) B4760689
theorem B6019915 : Blo 1670035 6019915 := bstep (se 1 (by rfl) ⟨4514936, by rfl⟩ : syracuseStep 6019915 = 9029873) B9029873
theorem B4758365 : Blo 1670035 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B2505611 : Blo 1670035 2505611 := bstep (se 1 (by rfl) ⟨1879208, by rfl⟩ : syracuseStep 2505611 = 3758417) B3758417
theorem B1670039 : Blo 1670035 1670039 := bstep (se 1 (by rfl) ⟨1252529, by rfl⟩ : syracuseStep 1670039 = 2505059) B2505059
theorem B2505623 : Blo 1670035 2505623 := bstep (se 1 (by rfl) ⟨1879217, by rfl⟩ : syracuseStep 2505623 = 3758435) B3758435
theorem B1670059 : Blo 1670035 1670059 := bstep (se 1 (by rfl) ⟨1252544, by rfl⟩ : syracuseStep 1670059 = 2505089) B2505089
theorem B13736881 : Blo 1670035 13736881 := bstep (se 2 (by rfl) ⟨5151330, by rfl⟩ : syracuseStep 13736881 = 10302661) B10302661
theorem B19037105 : Blo 1670035 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B7134131 : Blo 1670035 7134131 := bstep (se 1 (by rfl) ⟨5350598, by rfl⟩ : syracuseStep 7134131 = 10701197) B10701197
theorem B1670071 : Blo 1670035 1670071 := bstep (se 1 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 1670071 = 2505107) B2505107
theorem B1784759 : Blo 1670035 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B1670091 : Blo 1670035 1670091 := bstep (se 1 (by rfl) ⟨1252568, by rfl⟩ : syracuseStep 1670091 = 2505137) B2505137
theorem B1670103 : Blo 1670035 1670103 := bstep (se 1 (by rfl) ⟨1252577, by rfl⟩ : syracuseStep 1670103 = 2505155) B2505155
theorem B2505689 : Blo 1670035 2505689 := bstep (se 2 (by rfl) ⟨939633, by rfl⟩ : syracuseStep 2505689 = 1879267) B1879267
theorem B3759065 : Blo 1670035 3759065 := bstep (se 2 (by rfl) ⟨1409649, by rfl⟩ : syracuseStep 3759065 = 2819299) B2819299
theorem B1670123 : Blo 1670035 1670123 := bstep (se 1 (by rfl) ⟨1252592, by rfl⟩ : syracuseStep 1670123 = 2505185) B2505185
theorem B1670135 : Blo 1670035 1670135 := bstep (se 1 (by rfl) ⟨1252601, by rfl⟩ : syracuseStep 1670135 = 2505203) B2505203
theorem B1670155 : Blo 1670035 1670155 := bstep (se 1 (by rfl) ⟨1252616, by rfl⟩ : syracuseStep 1670155 = 2505233) B2505233
theorem B1694731 : Blo 1670035 1694731 := bstep (se 1 (by rfl) ⟨1271048, by rfl⟩ : syracuseStep 1694731 = 2542097) B2542097
theorem B1670167 : Blo 1670035 1670167 := bstep (se 1 (by rfl) ⟨1252625, by rfl⟩ : syracuseStep 1670167 = 2505251) B2505251
theorem B1670187 : Blo 1670035 1670187 := bstep (se 1 (by rfl) ⟨1252640, by rfl⟩ : syracuseStep 1670187 = 2505281) B2505281
theorem B3759155 : Blo 1670035 3759155 := bstep (se 1 (by rfl) ⟨2819366, by rfl⟩ : syracuseStep 3759155 = 5638733) B5638733
theorem B1670199 : Blo 1670035 1670199 := bstep (se 1 (by rfl) ⟨1252649, by rfl⟩ : syracuseStep 1670199 = 2505299) B2505299
theorem B1670219 : Blo 1670035 1670219 := bstep (se 1 (by rfl) ⟨1252664, by rfl⟩ : syracuseStep 1670219 = 2505329) B2505329
theorem B2505803 : Blo 1670035 2505803 := bstep (se 1 (by rfl) ⟨1879352, by rfl⟩ : syracuseStep 2505803 = 3758705) B3758705
theorem B1670231 : Blo 1670035 1670231 := bstep (se 1 (by rfl) ⟨1252673, by rfl⟩ : syracuseStep 1670231 = 2505347) B2505347
theorem B2505815 : Blo 1670035 2505815 := bstep (se 1 (by rfl) ⟨1879361, by rfl⟩ : syracuseStep 2505815 = 3758723) B3758723
theorem B3759191 : Blo 1670035 3759191 := bstep (se 1 (by rfl) ⟨2819393, by rfl⟩ : syracuseStep 3759191 = 5638787) B5638787
theorem B1670251 : Blo 1670035 1670251 := bstep (se 1 (by rfl) ⟨1252688, by rfl⟩ : syracuseStep 1670251 = 2505377) B2505377
theorem B1670263 : Blo 1670035 1670263 := bstep (se 1 (by rfl) ⟨1252697, by rfl⟩ : syracuseStep 1670263 = 2505395) B2505395
theorem B3570817 : Blo 1670035 3570817 := bstep (se 2 (by rfl) ⟨1339056, by rfl⟩ : syracuseStep 3570817 = 2678113) B2678113
theorem B1670283 : Blo 1670035 1670283 := bstep (se 1 (by rfl) ⟨1252712, by rfl⟩ : syracuseStep 1670283 = 2505425) B2505425
theorem B1670295 : Blo 1670035 1670295 := bstep (se 1 (by rfl) ⟨1252721, by rfl⟩ : syracuseStep 1670295 = 2505443) B2505443
theorem B2505881 : Blo 1670035 2505881 := bstep (se 2 (by rfl) ⟨939705, by rfl⟩ : syracuseStep 2505881 = 1879411) B1879411
theorem B1670315 : Blo 1670035 1670315 := bstep (se 1 (by rfl) ⟨1252736, by rfl⟩ : syracuseStep 1670315 = 2505473) B2505473
theorem B1670327 : Blo 1670035 1670327 := bstep (se 1 (by rfl) ⟨1252745, by rfl⟩ : syracuseStep 1670327 = 2505491) B2505491
theorem B1670347 : Blo 1670035 1670347 := bstep (se 1 (by rfl) ⟨1252760, by rfl⟩ : syracuseStep 1670347 = 2505521) B2505521
theorem B1670359 : Blo 1670035 1670359 := bstep (se 1 (by rfl) ⟨1252769, by rfl⟩ : syracuseStep 1670359 = 2505539) B2505539
theorem B1670379 : Blo 1670035 1670379 := bstep (se 1 (by rfl) ⟨1252784, by rfl⟩ : syracuseStep 1670379 = 2505569) B2505569
theorem B1670391 : Blo 1670035 1670391 := bstep (se 1 (by rfl) ⟨1252793, by rfl⟩ : syracuseStep 1670391 = 2505587) B2505587
theorem B1670411 : Blo 1670035 1670411 := bstep (se 1 (by rfl) ⟨1252808, by rfl⟩ : syracuseStep 1670411 = 2505617) B2505617
theorem B2505995 : Blo 1670035 2505995 := bstep (se 1 (by rfl) ⟨1879496, by rfl⟩ : syracuseStep 2505995 = 3758993) B3758993
theorem B3759371 : Blo 1670035 3759371 := bstep (se 1 (by rfl) ⟨2819528, by rfl⟩ : syracuseStep 3759371 = 5639057) B5639057
theorem B1670423 : Blo 1670035 1670423 := bstep (se 1 (by rfl) ⟨1252817, by rfl⟩ : syracuseStep 1670423 = 2505635) B2505635
theorem B2506007 : Blo 1670035 2506007 := bstep (se 1 (by rfl) ⟨1879505, by rfl⟩ : syracuseStep 2506007 = 3759011) B3759011
theorem B1670443 : Blo 1670035 1670443 := bstep (se 1 (by rfl) ⟨1252832, by rfl⟩ : syracuseStep 1670443 = 2505665) B2505665
theorem B1670455 : Blo 1670035 1670455 := bstep (se 1 (by rfl) ⟨1252841, by rfl⟩ : syracuseStep 1670455 = 2505683) B2505683
theorem B3759425 : Blo 1670035 3759425 := bstep (se 2 (by rfl) ⟨1409784, by rfl⟩ : syracuseStep 3759425 = 2819569) B2819569
theorem B1670475 : Blo 1670035 1670475 := bstep (se 1 (by rfl) ⟨1252856, by rfl⟩ : syracuseStep 1670475 = 2505713) B2505713
theorem B2006359 : Blo 1670035 2006359 := bstep (se 1 (by rfl) ⟨1504769, by rfl⟩ : syracuseStep 2006359 = 3009539) B3009539
theorem B1670487 : Blo 1670035 1670487 := bstep (se 1 (by rfl) ⟨1252865, by rfl⟩ : syracuseStep 1670487 = 2505731) B2505731
theorem B2506073 : Blo 1670035 2506073 := bstep (se 2 (by rfl) ⟨939777, by rfl⟩ : syracuseStep 2506073 = 1879555) B1879555
theorem B1670507 : Blo 1670035 1670507 := bstep (se 1 (by rfl) ⟨1252880, by rfl⟩ : syracuseStep 1670507 = 2505761) B2505761
theorem B1670519 : Blo 1670035 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B1670539 : Blo 1670035 1670539 := bstep (se 1 (by rfl) ⟨1252904, by rfl⟩ : syracuseStep 1670539 = 2505809) B2505809
theorem B1670551 : Blo 1670035 1670551 := bstep (se 1 (by rfl) ⟨1252913, by rfl⟩ : syracuseStep 1670551 = 2505827) B2505827
theorem B1670571 : Blo 1670035 1670571 := bstep (se 1 (by rfl) ⟨1252928, by rfl⟩ : syracuseStep 1670571 = 2505857) B2505857
theorem B1670583 : Blo 1670035 1670583 := bstep (se 1 (by rfl) ⟨1252937, by rfl⟩ : syracuseStep 1670583 = 2505875) B2505875
theorem B1670603 : Blo 1670035 1670603 := bstep (se 1 (by rfl) ⟨1252952, by rfl⟩ : syracuseStep 1670603 = 2505905) B2505905
theorem B2506187 : Blo 1670035 2506187 := bstep (se 1 (by rfl) ⟨1879640, by rfl⟩ : syracuseStep 2506187 = 3759281) B3759281
theorem B1670615 : Blo 1670035 1670615 := bstep (se 1 (by rfl) ⟨1252961, by rfl⟩ : syracuseStep 1670615 = 2505923) B2505923
theorem B2506199 : Blo 1670035 2506199 := bstep (se 1 (by rfl) ⟨1879649, by rfl⟩ : syracuseStep 2506199 = 3759299) B3759299
theorem B6348253 : Blo 1670035 6348253 := bstep (se 3 (by rfl) ⟨1190297, by rfl⟩ : syracuseStep 6348253 = 2380595) B2380595
theorem B1670635 : Blo 1670035 1670635 := bstep (se 1 (by rfl) ⟨1252976, by rfl⟩ : syracuseStep 1670635 = 2505953) B2505953
theorem B1670647 : Blo 1670035 1670647 := bstep (se 1 (by rfl) ⟨1252985, by rfl⟩ : syracuseStep 1670647 = 2505971) B2505971
theorem B1670667 : Blo 1670035 1670667 := bstep (se 1 (by rfl) ⟨1253000, by rfl⟩ : syracuseStep 1670667 = 2506001) B2506001
theorem B61840909 : Blo 1670035 61840909 := bstep (se 3 (by rfl) ⟨11595170, by rfl⟩ : syracuseStep 61840909 = 23190341) B23190341
theorem B1670679 : Blo 1670035 1670679 := bstep (se 1 (by rfl) ⟨1253009, by rfl⟩ : syracuseStep 1670679 = 2506019) B2506019
theorem B2506265 : Blo 1670035 2506265 := bstep (se 2 (by rfl) ⟨939849, by rfl⟩ : syracuseStep 2506265 = 1879699) B1879699
theorem B3759641 : Blo 1670035 3759641 := bstep (se 2 (by rfl) ⟨1409865, by rfl⟩ : syracuseStep 3759641 = 2819731) B2819731
theorem B1670699 : Blo 1670035 1670699 := bstep (se 1 (by rfl) ⟨1253024, by rfl⟩ : syracuseStep 1670699 = 2506049) B2506049
theorem B1670711 : Blo 1670035 1670711 := bstep (se 1 (by rfl) ⟨1253033, by rfl⟩ : syracuseStep 1670711 = 2506067) B2506067
theorem B1670731 : Blo 1670035 1670731 := bstep (se 1 (by rfl) ⟨1253048, by rfl⟩ : syracuseStep 1670731 = 2506097) B2506097
theorem B1670743 : Blo 1670035 1670743 := bstep (se 1 (by rfl) ⟨1253057, by rfl⟩ : syracuseStep 1670743 = 2506115) B2506115
theorem B8248925 : Blo 1670035 8248925 := bstep (se 3 (by rfl) ⟨1546673, by rfl⟩ : syracuseStep 8248925 = 3093347) B3093347
theorem B1670763 : Blo 1670035 1670763 := bstep (se 1 (by rfl) ⟨1253072, by rfl⟩ : syracuseStep 1670763 = 2506145) B2506145
theorem B3759731 : Blo 1670035 3759731 := bstep (se 1 (by rfl) ⟨2819798, by rfl⟩ : syracuseStep 3759731 = 5639597) B5639597
theorem B1670775 : Blo 1670035 1670775 := bstep (se 1 (by rfl) ⟨1253081, by rfl⟩ : syracuseStep 1670775 = 2506163) B2506163
theorem B1670795 : Blo 1670035 1670795 := bstep (se 1 (by rfl) ⟨1253096, by rfl⟩ : syracuseStep 1670795 = 2506193) B2506193
theorem B2506379 : Blo 1670035 2506379 := bstep (se 1 (by rfl) ⟨1879784, by rfl⟩ : syracuseStep 2506379 = 3759569) B3759569
theorem B1670807 : Blo 1670035 1670807 := bstep (se 1 (by rfl) ⟨1253105, by rfl⟩ : syracuseStep 1670807 = 2506211) B2506211
theorem B2506391 : Blo 1670035 2506391 := bstep (se 1 (by rfl) ⟨1879793, by rfl⟩ : syracuseStep 2506391 = 3759587) B3759587
theorem B3759767 : Blo 1670035 3759767 := bstep (se 1 (by rfl) ⟨2819825, by rfl⟩ : syracuseStep 3759767 = 5639651) B5639651
theorem B1670827 : Blo 1670035 1670827 := bstep (se 1 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 1670827 = 2506241) B2506241
theorem B1670839 : Blo 1670035 1670839 := bstep (se 1 (by rfl) ⟨1253129, by rfl⟩ : syracuseStep 1670839 = 2506259) B2506259
theorem B1670859 : Blo 1670035 1670859 := bstep (se 1 (by rfl) ⟨1253144, by rfl⟩ : syracuseStep 1670859 = 2506289) B2506289
theorem B1670871 : Blo 1670035 1670871 := bstep (se 1 (by rfl) ⟨1253153, by rfl⟩ : syracuseStep 1670871 = 2506307) B2506307
theorem B2506457 : Blo 1670035 2506457 := bstep (se 2 (by rfl) ⟨939921, by rfl⟩ : syracuseStep 2506457 = 1879843) B1879843
theorem B1670891 : Blo 1670035 1670891 := bstep (se 1 (by rfl) ⟨1253168, by rfl⟩ : syracuseStep 1670891 = 2506337) B2506337
theorem B1670903 : Blo 1670035 1670903 := bstep (se 1 (by rfl) ⟨1253177, by rfl⟩ : syracuseStep 1670903 = 2506355) B2506355
theorem B1670923 : Blo 1670035 1670923 := bstep (se 1 (by rfl) ⟨1253192, by rfl⟩ : syracuseStep 1670923 = 2506385) B2506385
theorem B1670935 : Blo 1670035 1670935 := bstep (se 1 (by rfl) ⟨1253201, by rfl⟩ : syracuseStep 1670935 = 2506403) B2506403
theorem B1670955 : Blo 1670035 1670955 := bstep (se 1 (by rfl) ⟨1253216, by rfl⟩ : syracuseStep 1670955 = 2506433) B2506433
theorem B1670967 : Blo 1670035 1670967 := bstep (se 1 (by rfl) ⟨1253225, by rfl⟩ : syracuseStep 1670967 = 2506451) B2506451
theorem B1670987 : Blo 1670035 1670987 := bstep (se 1 (by rfl) ⟨1253240, by rfl⟩ : syracuseStep 1670987 = 2506481) B2506481
theorem B2506571 : Blo 1670035 2506571 := bstep (se 1 (by rfl) ⟨1879928, by rfl⟩ : syracuseStep 2506571 = 3759857) B3759857
theorem B3759947 : Blo 1670035 3759947 := bstep (se 1 (by rfl) ⟨2819960, by rfl⟩ : syracuseStep 3759947 = 5639921) B5639921
theorem B5578571 : Blo 1670035 5578571 := bstep (se 1 (by rfl) ⟨4183928, by rfl⟩ : syracuseStep 5578571 = 8367857) B8367857
theorem B1670999 : Blo 1670035 1670999 := bstep (se 1 (by rfl) ⟨1253249, by rfl⟩ : syracuseStep 1670999 = 2506499) B2506499
theorem B2506583 : Blo 1670035 2506583 := bstep (se 1 (by rfl) ⟨1879937, by rfl⟩ : syracuseStep 2506583 = 3759875) B3759875
theorem B1671019 : Blo 1670035 1671019 := bstep (se 1 (by rfl) ⟨1253264, by rfl⟩ : syracuseStep 1671019 = 2506529) B2506529
theorem B1671031 : Blo 1670035 1671031 := bstep (se 1 (by rfl) ⟨1253273, by rfl⟩ : syracuseStep 1671031 = 2506547) B2506547
theorem B3760001 : Blo 1670035 3760001 := bstep (se 2 (by rfl) ⟨1410000, by rfl⟩ : syracuseStep 3760001 = 2820001) B2820001
theorem B1671051 : Blo 1670035 1671051 := bstep (se 1 (by rfl) ⟨1253288, by rfl⟩ : syracuseStep 1671051 = 2506577) B2506577
theorem B1671063 : Blo 1670035 1671063 := bstep (se 1 (by rfl) ⟨1253297, by rfl⟩ : syracuseStep 1671063 = 2506595) B2506595
theorem B8462231 : Blo 1670035 8462231 := bstep (se 1 (by rfl) ⟨6346673, by rfl⟩ : syracuseStep 8462231 = 12693347) B12693347
theorem B2506649 : Blo 1670035 2506649 := bstep (se 2 (by rfl) ⟨939993, by rfl⟩ : syracuseStep 2506649 = 1879987) B1879987
theorem B1671083 : Blo 1670035 1671083 := bstep (se 1 (by rfl) ⟨1253312, by rfl⟩ : syracuseStep 1671083 = 2506625) B2506625
theorem B65118131 : Blo 1670035 65118131 := bstep (se 1 (by rfl) ⟨48838598, by rfl⟩ : syracuseStep 65118131 = 97677197) B97677197
theorem B1671095 : Blo 1670035 1671095 := bstep (se 1 (by rfl) ⟨1253321, by rfl⟩ : syracuseStep 1671095 = 2506643) B2506643
theorem B1671115 : Blo 1670035 1671115 := bstep (se 1 (by rfl) ⟨1253336, by rfl⟩ : syracuseStep 1671115 = 2506673) B2506673
theorem B1671127 : Blo 1670035 1671127 := bstep (se 1 (by rfl) ⟨1253345, by rfl⟩ : syracuseStep 1671127 = 2506691) B2506691
theorem B1671147 : Blo 1670035 1671147 := bstep (se 1 (by rfl) ⟨1253360, by rfl⟩ : syracuseStep 1671147 = 2506721) B2506721
theorem B1671159 : Blo 1670035 1671159 := bstep (se 1 (by rfl) ⟨1253369, by rfl⟩ : syracuseStep 1671159 = 2506739) B2506739
theorem B1671175 : Blo 1670035 1671175 := bstep (se 1 (by rfl) ⟨1253381, by rfl⟩ : syracuseStep 1671175 = 2506763) B2506763
theorem B1671183 : Blo 1670035 1671183 := bstep (se 1 (by rfl) ⟨1253387, by rfl⟩ : syracuseStep 1671183 = 2506775) B2506775
theorem B2506811 : Blo 1670035 2506811 := bstep (se 1 (by rfl) ⟨1880108, by rfl⟩ : syracuseStep 2506811 = 3760217) B3760217
theorem B1671227 : Blo 1670035 1671227 := bstep (se 1 (by rfl) ⟨1253420, by rfl⟩ : syracuseStep 1671227 = 2506841) B2506841
theorem B16056407 : Blo 1670035 16056407 := bstep (se 1 (by rfl) ⟨12042305, by rfl⟩ : syracuseStep 16056407 = 24084611) B24084611
theorem B9519191 : Blo 1670035 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B2539639 : Blo 1670035 2539639 := bstep (se 1 (by rfl) ⟨1904729, by rfl⟩ : syracuseStep 2539639 = 3809459) B3809459
theorem B2506871 : Blo 1670035 2506871 := bstep (se 1 (by rfl) ⟨1880153, by rfl⟩ : syracuseStep 2506871 = 3760307) B3760307
theorem B1671303 : Blo 1670035 1671303 := bstep (se 1 (by rfl) ⟨1253477, by rfl⟩ : syracuseStep 1671303 = 2506955) B2506955
theorem B2506895 : Blo 1670035 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B1671311 : Blo 1670035 1671311 := bstep (se 1 (by rfl) ⟨1253483, by rfl⟩ : syracuseStep 1671311 = 2506967) B2506967
theorem B2506937 : Blo 1670035 2506937 := bstep (se 2 (by rfl) ⟨940101, by rfl⟩ : syracuseStep 2506937 = 1880203) B1880203
theorem B1671355 : Blo 1670035 1671355 := bstep (se 1 (by rfl) ⟨1253516, by rfl⟩ : syracuseStep 1671355 = 2507033) B2507033
theorem B11436233 : Blo 1670035 11436233 := bstep (se 2 (by rfl) ⟨4288587, by rfl⟩ : syracuseStep 11436233 = 8577175) B8577175
theorem B4227329 : Blo 1670035 4227329 := bstep (se 2 (by rfl) ⟨1585248, by rfl⟩ : syracuseStep 4227329 = 3170497) B3170497
theorem B2507015 : Blo 1670035 2507015 := bstep (se 1 (by rfl) ⟨1880261, by rfl⟩ : syracuseStep 2507015 = 3760523) B3760523
theorem B1671431 : Blo 1670035 1671431 := bstep (se 1 (by rfl) ⟨1253573, by rfl⟩ : syracuseStep 1671431 = 2507147) B2507147
theorem B1671439 : Blo 1670035 1671439 := bstep (se 1 (by rfl) ⟨1253579, by rfl⟩ : syracuseStep 1671439 = 2507159) B2507159
theorem B20316433 : Blo 1670035 20316433 := bstep (se 2 (by rfl) ⟨7618662, by rfl⟩ : syracuseStep 20316433 = 15237325) B15237325
theorem B4759823 : Blo 1670035 4759823 := bstep (se 1 (by rfl) ⟨3569867, by rfl⟩ : syracuseStep 4759823 = 7139735) B7139735
theorem B3170603 : Blo 1670035 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B2507051 : Blo 1670035 2507051 := bstep (se 1 (by rfl) ⟨1880288, by rfl⟩ : syracuseStep 2507051 = 3760577) B3760577
theorem B5636411 : Blo 1670035 5636411 := bstep (se 1 (by rfl) ⟨4227308, by rfl⟩ : syracuseStep 5636411 = 8454617) B8454617
theorem B2007355 : Blo 1670035 2007355 := bstep (se 1 (by rfl) ⟨1505516, by rfl⟩ : syracuseStep 2007355 = 3011033) B3011033
theorem B1671483 : Blo 1670035 1671483 := bstep (se 1 (by rfl) ⟨1253612, by rfl⟩ : syracuseStep 1671483 = 2507225) B2507225
theorem B2507081 : Blo 1670035 2507081 := bstep (se 2 (by rfl) ⟨940155, by rfl⟩ : syracuseStep 2507081 = 1880311) B1880311
theorem B1671559 : Blo 1670035 1671559 := bstep (se 1 (by rfl) ⟨1253669, by rfl⟩ : syracuseStep 1671559 = 2507339) B2507339
theorem B1671567 : Blo 1670035 1671567 := bstep (se 1 (by rfl) ⟨1253675, by rfl⟩ : syracuseStep 1671567 = 2507351) B2507351
theorem B2818489 : Blo 1670035 2818489 := bstep (se 2 (by rfl) ⟨1056933, by rfl⟩ : syracuseStep 2818489 = 2113867) B2113867
theorem B2507195 : Blo 1670035 2507195 := bstep (se 1 (by rfl) ⟨1880396, by rfl⟩ : syracuseStep 2507195 = 3760793) B3760793
theorem B1671611 : Blo 1670035 1671611 := bstep (se 1 (by rfl) ⟨1253708, by rfl⟩ : syracuseStep 1671611 = 2507417) B2507417
theorem B2114039 : Blo 1670035 2114039 := bstep (se 1 (by rfl) ⟨1585529, by rfl⟩ : syracuseStep 2114039 = 3171059) B3171059
theorem B2507255 : Blo 1670035 2507255 := bstep (se 1 (by rfl) ⟨1880441, by rfl⟩ : syracuseStep 2507255 = 3760883) B3760883
theorem B1671687 : Blo 1670035 1671687 := bstep (se 1 (by rfl) ⟨1253765, by rfl⟩ : syracuseStep 1671687 = 2507531) B2507531
theorem B2507279 : Blo 1670035 2507279 := bstep (se 1 (by rfl) ⟨1880459, by rfl⟩ : syracuseStep 2507279 = 3760919) B3760919
theorem B1671695 : Blo 1670035 1671695 := bstep (se 1 (by rfl) ⟨1253771, by rfl⟩ : syracuseStep 1671695 = 2507543) B2507543
theorem B3809825 : Blo 1670035 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B2507321 : Blo 1670035 2507321 := bstep (se 2 (by rfl) ⟨940245, by rfl⟩ : syracuseStep 2507321 = 1880491) B1880491
theorem B1671739 : Blo 1670035 1671739 := bstep (se 1 (by rfl) ⟨1253804, by rfl⟩ : syracuseStep 1671739 = 2507609) B2507609
theorem B4014679 : Blo 1670035 4014679 := bstep (se 1 (by rfl) ⟨3011009, by rfl⟩ : syracuseStep 4014679 = 6022019) B6022019
theorem B3760775 : Blo 1670035 3760775 := bstep (se 1 (by rfl) ⟨2820581, by rfl⟩ : syracuseStep 3760775 = 5641163) B5641163
theorem B2507399 : Blo 1670035 2507399 := bstep (se 1 (by rfl) ⟨1880549, by rfl⟩ : syracuseStep 2507399 = 3761099) B3761099
theorem B1671815 : Blo 1670035 1671815 := bstep (se 1 (by rfl) ⟨1253861, by rfl⟩ : syracuseStep 1671815 = 2507723) B2507723
theorem B2114191 : Blo 1670035 2114191 := bstep (se 1 (by rfl) ⟨1585643, by rfl⟩ : syracuseStep 2114191 = 3171287) B3171287
theorem B1671823 : Blo 1670035 1671823 := bstep (se 1 (by rfl) ⟨1253867, by rfl⟩ : syracuseStep 1671823 = 2507735) B2507735
theorem B2507435 : Blo 1670035 2507435 := bstep (se 1 (by rfl) ⟨1880576, by rfl⟩ : syracuseStep 2507435 = 3761153) B3761153
theorem B1671867 : Blo 1670035 1671867 := bstep (se 1 (by rfl) ⟨1253900, by rfl⟩ : syracuseStep 1671867 = 2507801) B2507801
theorem B8463041 : Blo 1670035 8463041 := bstep (se 2 (by rfl) ⟨3173640, by rfl⟩ : syracuseStep 8463041 = 6347281) B6347281
theorem B4227785 : Blo 1670035 4227785 := bstep (se 2 (by rfl) ⟨1585419, by rfl⟩ : syracuseStep 4227785 = 3170839) B3170839
theorem B2507465 : Blo 1670035 2507465 := bstep (se 2 (by rfl) ⟨940299, by rfl⟩ : syracuseStep 2507465 = 1880599) B1880599
theorem B16278245 : Blo 1670035 16278245 := bstep (se 4 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 16278245 = 3052171) B3052171
theorem B1671943 : Blo 1670035 1671943 := bstep (se 1 (by rfl) ⟨1253957, by rfl⟩ : syracuseStep 1671943 = 2507915) B2507915
theorem B1671951 : Blo 1670035 1671951 := bstep (se 1 (by rfl) ⟨1253963, by rfl⟩ : syracuseStep 1671951 = 2507927) B2507927
theorem B5636897 : Blo 1670035 5636897 := bstep (se 2 (by rfl) ⟨2113836, by rfl⟩ : syracuseStep 5636897 = 4227673) B4227673
theorem B6341435 : Blo 1670035 6341435 := bstep (se 1 (by rfl) ⟨4756076, by rfl⟩ : syracuseStep 6341435 = 9512153) B9512153
theorem B2114363 : Blo 1670035 2114363 := bstep (se 1 (by rfl) ⟨1585772, by rfl⟩ : syracuseStep 2114363 = 3171545) B3171545
theorem B3760955 : Blo 1670035 3760955 := bstep (se 1 (by rfl) ⟨2820716, by rfl⟩ : syracuseStep 3760955 = 5641433) B5641433
theorem B2507579 : Blo 1670035 2507579 := bstep (se 1 (by rfl) ⟨1880684, by rfl⟩ : syracuseStep 2507579 = 3761369) B3761369
theorem B1671995 : Blo 1670035 1671995 := bstep (se 1 (by rfl) ⟨1253996, by rfl⟩ : syracuseStep 1671995 = 2507993) B2507993
theorem B2507639 : Blo 1670035 2507639 := bstep (se 1 (by rfl) ⟨1880729, by rfl⟩ : syracuseStep 2507639 = 3761459) B3761459
theorem B2507663 : Blo 1670035 2507663 := bstep (se 1 (by rfl) ⟨1880747, by rfl⟩ : syracuseStep 2507663 = 3761495) B3761495
theorem B3761081 : Blo 1670035 3761081 := bstep (se 2 (by rfl) ⟨1410405, by rfl⟩ : syracuseStep 3761081 = 2820811) B2820811
theorem B2507705 : Blo 1670035 2507705 := bstep (se 2 (by rfl) ⟨940389, by rfl⟩ : syracuseStep 2507705 = 1880779) B1880779
theorem B9511901 : Blo 1670035 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B2507783 : Blo 1670035 2507783 := bstep (se 1 (by rfl) ⟨1880837, by rfl⟩ : syracuseStep 2507783 = 3761675) B3761675
theorem B4514827 : Blo 1670035 4514827 := bstep (se 1 (by rfl) ⟨3386120, by rfl⟩ : syracuseStep 4514827 = 6772241) B6772241
theorem B4228139 : Blo 1670035 4228139 := bstep (se 1 (by rfl) ⟨3171104, by rfl⟩ : syracuseStep 4228139 = 6342209) B6342209
theorem B2507819 : Blo 1670035 2507819 := bstep (se 1 (by rfl) ⟨1880864, by rfl⟩ : syracuseStep 2507819 = 3761729) B3761729
theorem B2507849 : Blo 1670035 2507849 := bstep (se 2 (by rfl) ⟨940443, by rfl⟩ : syracuseStep 2507849 = 1880887) B1880887
theorem B2819191 : Blo 1670035 2819191 := bstep (se 1 (by rfl) ⟨2114393, by rfl⟩ : syracuseStep 2819191 = 4228787) B4228787
theorem B14279813 : Blo 1670035 14279813 := bstep (se 4 (by rfl) ⟨1338732, by rfl⟩ : syracuseStep 14279813 = 2677465) B2677465
theorem B2507963 : Blo 1670035 2507963 := bstep (se 1 (by rfl) ⟨1880972, by rfl⟩ : syracuseStep 2507963 = 3761945) B3761945
theorem B2508023 : Blo 1670035 2508023 := bstep (se 1 (by rfl) ⟨1881017, by rfl⟩ : syracuseStep 2508023 = 3762035) B3762035
theorem B3761423 : Blo 1670035 3761423 := bstep (se 1 (by rfl) ⟨2821067, by rfl⟩ : syracuseStep 3761423 = 5642135) B5642135
theorem B2508047 : Blo 1670035 2508047 := bstep (se 1 (by rfl) ⟨1881035, by rfl⟩ : syracuseStep 2508047 = 3762071) B3762071
theorem B6341921 : Blo 1670035 6341921 := bstep (se 2 (by rfl) ⟨2378220, by rfl⟩ : syracuseStep 6341921 = 4756441) B4756441
theorem B3761441 : Blo 1670035 3761441 := bstep (se 2 (by rfl) ⟨1410540, by rfl⟩ : syracuseStep 3761441 = 2821081) B2821081
theorem B2819387 : Blo 1670035 2819387 := bstep (se 1 (by rfl) ⟨2114540, by rfl⟩ : syracuseStep 2819387 = 4229081) B4229081
theorem B5637491 : Blo 1670035 5637491 := bstep (se 1 (by rfl) ⟨4228118, by rfl⟩ : syracuseStep 5637491 = 8456237) B8456237
theorem B4015507 : Blo 1670035 4015507 := bstep (se 1 (by rfl) ⟨3011630, by rfl⟩ : syracuseStep 4015507 = 6023261) B6023261
theorem B15246739 : Blo 1670035 15246739 := bstep (se 1 (by rfl) ⟨11435054, by rfl⟩ : syracuseStep 15246739 = 22870109) B22870109
theorem B9037265 : Blo 1670035 9037265 := bstep (se 2 (by rfl) ⟨3388974, by rfl⟩ : syracuseStep 9037265 = 6777949) B6777949
theorem B4761089 : Blo 1670035 4761089 := bstep (se 2 (by rfl) ⟨1785408, by rfl⟩ : syracuseStep 4761089 = 3570817) B3570817
theorem B2352655 : Blo 1670035 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B3761783 : Blo 1670035 3761783 := bstep (se 1 (by rfl) ⟨2821337, by rfl⟩ : syracuseStep 3761783 = 5642675) B5642675
theorem B2819785 : Blo 1670035 2819785 := bstep (se 2 (by rfl) ⟨1057419, by rfl⟩ : syracuseStep 2819785 = 2114839) B2114839
theorem B2115335 : Blo 1670035 2115335 := bstep (se 1 (by rfl) ⟨1586501, by rfl⟩ : syracuseStep 2115335 = 3173003) B3173003
theorem B10700581 : Blo 1670035 10700581 := bstep (se 4 (by rfl) ⟨1003179, by rfl⟩ : syracuseStep 10700581 = 2006359) B2006359
theorem B3761963 : Blo 1670035 3761963 := bstep (se 1 (by rfl) ⟨2821472, by rfl⟩ : syracuseStep 3761963 = 5642945) B5642945
theorem B14280563 : Blo 1670035 14280563 := bstep (se 1 (by rfl) ⟨10710422, by rfl⟩ : syracuseStep 14280563 = 21420845) B21420845
theorem B9652121 : Blo 1670035 9652121 := bstep (se 2 (by rfl) ⟨3619545, by rfl⟩ : syracuseStep 9652121 = 7239091) B7239091
theorem B3172297 : Blo 1670035 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B12691403 : Blo 1670035 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B8464337 : Blo 1670035 8464337 := bstep (se 2 (by rfl) ⟨3174126, by rfl⟩ : syracuseStep 8464337 = 6348253) B6348253
theorem B4229131 : Blo 1670035 4229131 := bstep (se 1 (by rfl) ⟨3171848, by rfl⟩ : syracuseStep 4229131 = 6343697) B6343697
theorem B82454545 : Blo 1670035 82454545 := bstep (se 2 (by rfl) ⟨30920454, by rfl⟩ : syracuseStep 82454545 = 61840909) B61840909
theorem B4229273 : Blo 1670035 4229273 := bstep (se 2 (by rfl) ⟨1585977, by rfl⟩ : syracuseStep 4229273 = 3171955) B3171955
theorem B6342893 : Blo 1670035 6342893 := bstep (se 3 (by rfl) ⟨1189292, by rfl⟩ : syracuseStep 6342893 = 2378585) B2378585
theorem B4229435 : Blo 1670035 4229435 := bstep (se 1 (by rfl) ⟨3172076, by rfl⟩ : syracuseStep 4229435 = 6344153) B6344153
theorem B2820487 : Blo 1670035 2820487 := bstep (se 1 (by rfl) ⟨2115365, by rfl⟩ : syracuseStep 2820487 = 4230731) B4230731
theorem B2115983 : Blo 1670035 2115983 := bstep (se 1 (by rfl) ⟨1586987, by rfl⟩ : syracuseStep 2115983 = 3173975) B3173975
theorem B5499283 : Blo 1670035 5499283 := bstep (se 1 (by rfl) ⟨4124462, by rfl⟩ : syracuseStep 5499283 = 8248925) B8248925
theorem B7137821 : Blo 1670035 7137821 := bstep (se 3 (by rfl) ⟨1338341, by rfl⟩ : syracuseStep 7137821 = 2676683) B2676683
theorem B6343211 : Blo 1670035 6343211 := bstep (se 1 (by rfl) ⟨4757408, by rfl⟩ : syracuseStep 6343211 = 9514817) B9514817
theorem B43412087 : Blo 1670035 43412087 := bstep (se 1 (by rfl) ⟨32559065, by rfl⟩ : syracuseStep 43412087 = 65118131) B65118131
theorem B4229779 : Blo 1670035 4229779 := bstep (se 1 (by rfl) ⟨3172334, by rfl⟩ : syracuseStep 4229779 = 6344669) B6344669
theorem B1878799 : Blo 1670035 1878799 := bstep (se 1 (by rfl) ⟨1409099, by rfl⟩ : syracuseStep 1878799 = 2818199) B2818199
theorem B4229921 : Blo 1670035 4229921 := bstep (se 2 (by rfl) ⟨1586220, by rfl⟩ : syracuseStep 4229921 = 3172441) B3172441
theorem B36129685 : Blo 1670035 36129685 := bstep (se 6 (by rfl) ⟨846789, by rfl⟩ : syracuseStep 36129685 = 1693579) B1693579
theorem B16067479 : Blo 1670035 16067479 := bstep (se 1 (by rfl) ⟨12050609, by rfl⟩ : syracuseStep 16067479 = 24101219) B24101219
theorem B20327435 : Blo 1670035 20327435 := bstep (se 1 (by rfl) ⟨15245576, by rfl⟩ : syracuseStep 20327435 = 30491153) B30491153
theorem B2821135 : Blo 1670035 2821135 := bstep (se 1 (by rfl) ⟨2115851, by rfl⟩ : syracuseStep 2821135 = 4231703) B4231703
theorem B7334941 : Blo 1670035 7334941 := bstep (se 3 (by rfl) ⟨1375301, by rfl⟩ : syracuseStep 7334941 = 2750603) B2750603
theorem B7138505 : Blo 1670035 7138505 := bstep (se 2 (by rfl) ⟨2676939, by rfl⟩ : syracuseStep 7138505 = 5353879) B5353879
theorem B1879303 : Blo 1670035 1879303 := bstep (se 1 (by rfl) ⟨1409477, by rfl⟩ : syracuseStep 1879303 = 2818955) B2818955
theorem B1879483 : Blo 1670035 1879483 := bstep (se 1 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 1879483 = 2819225) B2819225
theorem B97643981 : Blo 1670035 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B16281091 : Blo 1670035 16281091 := bstep (se 1 (by rfl) ⟨12210818, by rfl⟩ : syracuseStep 16281091 = 24421637) B24421637
theorem B7237187 : Blo 1670035 7237187 := bstep (se 1 (by rfl) ⟨5427890, by rfl⟩ : syracuseStep 7237187 = 10855781) B10855781
theorem B2379451 : Blo 1670035 2379451 := bstep (se 1 (by rfl) ⟨1784588, by rfl⟩ : syracuseStep 2379451 = 3569177) B3569177
theorem B10161865 : Blo 1670035 10161865 := bstep (se 2 (by rfl) ⟨3810699, by rfl⟩ : syracuseStep 10161865 = 7621399) B7621399
theorem B4230913 : Blo 1670035 4230913 := bstep (se 2 (by rfl) ⟨1586592, by rfl⟩ : syracuseStep 4230913 = 3173185) B3173185
theorem B7139087 : Blo 1670035 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B3174203 : Blo 1670035 3174203 := bstep (se 1 (by rfl) ⟨2380652, by rfl⟩ : syracuseStep 3174203 = 4761305) B4761305
theorem B1879951 : Blo 1670035 1879951 := bstep (se 1 (by rfl) ⟨1409963, by rfl⟩ : syracuseStep 1879951 = 2819927) B2819927
theorem B5640083 : Blo 1670035 5640083 := bstep (se 1 (by rfl) ⟨4230062, by rfl⟩ : syracuseStep 5640083 = 8460125) B8460125
theorem B3051535 : Blo 1670035 3051535 := bstep (se 1 (by rfl) ⟨2288651, by rfl⟩ : syracuseStep 3051535 = 4577303) B4577303
theorem B9515069 : Blo 1670035 9515069 := bstep (se 3 (by rfl) ⟨1784075, by rfl⟩ : syracuseStep 9515069 = 3568151) B3568151
theorem B7139447 : Blo 1670035 7139447 := bstep (se 1 (by rfl) ⟨5354585, by rfl⟩ : syracuseStep 7139447 = 10709171) B10709171
theorem B3567817 : Blo 1670035 3567817 := bstep (se 2 (by rfl) ⟨1337931, by rfl⟩ : syracuseStep 3567817 = 2675863) B2675863
theorem B3010859 : Blo 1670035 3010859 := bstep (se 1 (by rfl) ⟨2258144, by rfl⟩ : syracuseStep 3010859 = 4516289) B4516289
theorem B4231511 : Blo 1670035 4231511 := bstep (se 1 (by rfl) ⟨3173633, by rfl⟩ : syracuseStep 4231511 = 6347267) B6347267
theorem B2380151 : Blo 1670035 2380151 := bstep (se 1 (by rfl) ⟨1785113, by rfl⟩ : syracuseStep 2380151 = 3570227) B3570227
theorem B1880455 : Blo 1670035 1880455 := bstep (se 1 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 1880455 = 2820683) B2820683
theorem B13545913 : Blo 1670035 13545913 := bstep (se 2 (by rfl) ⟨5079717, by rfl⟩ : syracuseStep 13545913 = 10159435) B10159435
theorem B6025681 : Blo 1670035 6025681 := bstep (se 2 (by rfl) ⟨2259630, by rfl⟩ : syracuseStep 6025681 = 4519261) B4519261
theorem B2675243 : Blo 1670035 2675243 := bstep (se 1 (by rfl) ⟨2006432, by rfl⟩ : syracuseStep 2675243 = 4012865) B4012865
theorem B4231723 : Blo 1670035 4231723 := bstep (se 1 (by rfl) ⟨3173792, by rfl⟩ : syracuseStep 4231723 = 6347585) B6347585
theorem B487862837 : Blo 1670035 487862837 := bstep (se 5 (by rfl) ⟨22868570, by rfl⟩ : syracuseStep 487862837 = 45737141) B45737141
theorem B1880635 : Blo 1670035 1880635 := bstep (se 1 (by rfl) ⟨1410476, by rfl⟩ : syracuseStep 1880635 = 2820953) B2820953
theorem B4756087 : Blo 1670035 4756087 := bstep (se 1 (by rfl) ⟨3567065, by rfl⟩ : syracuseStep 4756087 = 7134131) B7134131
theorem B3568313 : Blo 1670035 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B4231865 : Blo 1670035 4231865 := bstep (se 2 (by rfl) ⟨1586949, by rfl⟩ : syracuseStep 4231865 = 3173899) B3173899
theorem B32125733 : Blo 1670035 32125733 := bstep (se 4 (by rfl) ⟨3011787, by rfl⟩ : syracuseStep 32125733 = 6023575) B6023575
theorem B8459153 : Blo 1670035 8459153 := bstep (se 2 (by rfl) ⟨3172182, by rfl⟩ : syracuseStep 8459153 = 6344365) B6344365
theorem B7140419 : Blo 1670035 7140419 := bstep (se 1 (by rfl) ⟨5355314, by rfl⟩ : syracuseStep 7140419 = 10710629) B10710629
theorem B2061559 : Blo 1670035 2061559 := bstep (se 1 (by rfl) ⟨1546169, by rfl⟩ : syracuseStep 2061559 = 3092339) B3092339
theorem B5641487 : Blo 1670035 5641487 := bstep (se 1 (by rfl) ⟨4231115, by rfl⟩ : syracuseStep 5641487 = 8462231) B8462231
theorem B18060691 : Blo 1670035 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B7140761 : Blo 1670035 7140761 := bstep (se 2 (by rfl) ⟨2677785, by rfl⟩ : syracuseStep 7140761 = 5355571) B5355571
theorem B6772177 : Blo 1670035 6772177 := bstep (se 2 (by rfl) ⟨2539566, by rfl⟩ : syracuseStep 6772177 = 5079133) B5079133
theorem B3388943 : Blo 1670035 3388943 := bstep (se 1 (by rfl) ⟨2541707, by rfl⟩ : syracuseStep 3388943 = 5083415) B5083415
theorem B5641757 : Blo 1670035 5641757 := bstep (se 3 (by rfl) ⟨1057829, by rfl⟩ : syracuseStep 5641757 = 2115659) B2115659
theorem B3569287 : Blo 1670035 3569287 := bstep (se 1 (by rfl) ⟨2676965, by rfl⟩ : syracuseStep 3569287 = 5353931) B5353931
theorem B3757715 : Blo 1670035 3757715 := bstep (se 1 (by rfl) ⟨2818286, by rfl⟩ : syracuseStep 3757715 = 5636573) B5636573
theorem B4519577 : Blo 1670035 4519577 := bstep (se 2 (by rfl) ⟨1694841, by rfl⟩ : syracuseStep 4519577 = 3389683) B3389683
theorem B8935105 : Blo 1670035 8935105 := bstep (se 2 (by rfl) ⟨3350664, by rfl⟩ : syracuseStep 8935105 = 6701329) B6701329
theorem B3757769 : Blo 1670035 3757769 := bstep (se 2 (by rfl) ⟨1409163, by rfl⟩ : syracuseStep 3757769 = 2818327) B2818327
theorem B1783567 : Blo 1670035 1783567 := bstep (se 1 (by rfl) ⟨1337675, by rfl⟩ : syracuseStep 1783567 = 2675351) B2675351
theorem B4757363 : Blo 1670035 4757363 := bstep (se 1 (by rfl) ⟨3568022, by rfl⟩ : syracuseStep 4757363 = 7136045) B7136045
theorem B6772747 : Blo 1670035 6772747 := bstep (se 1 (by rfl) ⟨5079560, by rfl⟩ : syracuseStep 6772747 = 10159121) B10159121
theorem B6346781 : Blo 1670035 6346781 := bstep (se 3 (by rfl) ⟨1190021, by rfl⟩ : syracuseStep 6346781 = 2380043) B2380043
theorem B6346795 : Blo 1670035 6346795 := bstep (se 1 (by rfl) ⟨4760096, by rfl⟩ : syracuseStep 6346795 = 9520193) B9520193
theorem B4823101 : Blo 1670035 4823101 := bstep (se 3 (by rfl) ⟨904331, by rfl⟩ : syracuseStep 4823101 = 1808663) B1808663
theorem B4757591 : Blo 1670035 4757591 := bstep (se 1 (by rfl) ⟨3568193, by rfl⟩ : syracuseStep 4757591 = 7136387) B7136387
theorem B2505095 : Blo 1670035 2505095 := bstep (se 1 (by rfl) ⟨1878821, by rfl⟩ : syracuseStep 2505095 = 3757643) B3757643
theorem B3758471 : Blo 1670035 3758471 := bstep (se 1 (by rfl) ⟨2818853, by rfl⟩ : syracuseStep 3758471 = 5637707) B5637707
theorem B10705297 : Blo 1670035 10705297 := bstep (se 2 (by rfl) ⟨4014486, by rfl⟩ : syracuseStep 10705297 = 8028973) B8028973
theorem B9517459 : Blo 1670035 9517459 := bstep (se 1 (by rfl) ⟨7138094, by rfl⟩ : syracuseStep 9517459 = 14276189) B14276189
theorem B5355929 : Blo 1670035 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B2505131 : Blo 1670035 2505131 := bstep (se 1 (by rfl) ⟨1878848, by rfl⟩ : syracuseStep 2505131 = 3757697) B3757697
theorem B8026553 : Blo 1670035 8026553 := bstep (se 2 (by rfl) ⟨3009957, by rfl⟩ : syracuseStep 8026553 = 6019915) B6019915
theorem B2505161 : Blo 1670035 2505161 := bstep (se 2 (by rfl) ⟨939435, by rfl⟩ : syracuseStep 2505161 = 1878871) B1878871
theorem B8026667 : Blo 1670035 8026667 := bstep (se 1 (by rfl) ⟨6020000, by rfl⟩ : syracuseStep 8026667 = 12040001) B12040001
theorem B2505275 : Blo 1670035 2505275 := bstep (se 1 (by rfl) ⟨1878956, by rfl⟩ : syracuseStep 2505275 = 3757913) B3757913
theorem B3758651 : Blo 1670035 3758651 := bstep (se 1 (by rfl) ⟨2818988, by rfl⟩ : syracuseStep 3758651 = 5637977) B5637977
theorem B18315841 : Blo 1670035 18315841 := bstep (se 2 (by rfl) ⟨6868440, by rfl⟩ : syracuseStep 18315841 = 13736881) B13736881
theorem B2505335 : Blo 1670035 2505335 := bstep (se 1 (by rfl) ⟨1879001, by rfl⟩ : syracuseStep 2505335 = 3758003) B3758003
theorem B2505359 : Blo 1670035 2505359 := bstep (se 1 (by rfl) ⟨1879019, by rfl⟩ : syracuseStep 2505359 = 3758039) B3758039
theorem B2505401 : Blo 1670035 2505401 := bstep (se 2 (by rfl) ⟨939525, by rfl⟩ : syracuseStep 2505401 = 1879051) B1879051
theorem B3758777 : Blo 1670035 3758777 := bstep (se 2 (by rfl) ⟨1409541, by rfl⟩ : syracuseStep 3758777 = 2819083) B2819083
theorem B2259641 : Blo 1670035 2259641 := bstep (se 2 (by rfl) ⟨847365, by rfl⟩ : syracuseStep 2259641 = 1694731) B1694731
theorem B2505479 : Blo 1670035 2505479 := bstep (se 1 (by rfl) ⟨1879109, by rfl⟩ : syracuseStep 2505479 = 3758219) B3758219
theorem B2505515 : Blo 1670035 2505515 := bstep (se 1 (by rfl) ⟨1879136, by rfl⟩ : syracuseStep 2505515 = 3758273) B3758273
theorem B3570475 : Blo 1670035 3570475 := bstep (se 1 (by rfl) ⟨2677856, by rfl⟩ : syracuseStep 3570475 = 5355713) B5355713
theorem B2505545 : Blo 1670035 2505545 := bstep (se 2 (by rfl) ⟨939579, by rfl⟩ : syracuseStep 2505545 = 1879159) B1879159
theorem B1670075 : Blo 1670035 1670075 := bstep (se 1 (by rfl) ⟨1252556, by rfl⟩ : syracuseStep 1670075 = 2505113) B2505113
theorem B2505659 : Blo 1670035 2505659 := bstep (se 1 (by rfl) ⟨1879244, by rfl⟩ : syracuseStep 2505659 = 3758489) B3758489
theorem B8461259 : Blo 1670035 8461259 := bstep (se 1 (by rfl) ⟨6345944, by rfl⟩ : syracuseStep 8461259 = 12691889) B12691889
theorem B2505719 : Blo 1670035 2505719 := bstep (se 1 (by rfl) ⟨1879289, by rfl⟩ : syracuseStep 2505719 = 3758579) B3758579
theorem B1670151 : Blo 1670035 1670151 := bstep (se 1 (by rfl) ⟨1252613, by rfl⟩ : syracuseStep 1670151 = 2505227) B2505227
theorem B1670159 : Blo 1670035 1670159 := bstep (se 1 (by rfl) ⟨1252619, by rfl⟩ : syracuseStep 1670159 = 2505239) B2505239
theorem B2505743 : Blo 1670035 2505743 := bstep (se 1 (by rfl) ⟨1879307, by rfl⟩ : syracuseStep 2505743 = 3758615) B3758615
theorem B3759119 : Blo 1670035 3759119 := bstep (se 1 (by rfl) ⟨2819339, by rfl⟩ : syracuseStep 3759119 = 5638679) B5638679
theorem B3759137 : Blo 1670035 3759137 := bstep (se 2 (by rfl) ⟨1409676, by rfl⟩ : syracuseStep 3759137 = 2819353) B2819353
theorem B2505785 : Blo 1670035 2505785 := bstep (se 2 (by rfl) ⟨939669, by rfl⟩ : syracuseStep 2505785 = 1879339) B1879339
theorem B1670203 : Blo 1670035 1670203 := bstep (se 1 (by rfl) ⟨1252652, by rfl⟩ : syracuseStep 1670203 = 2505305) B2505305
theorem B18062423 : Blo 1670035 18062423 := bstep (se 1 (by rfl) ⟨13546817, by rfl⟩ : syracuseStep 18062423 = 27093635) B27093635
theorem B1670279 : Blo 1670035 1670279 := bstep (se 1 (by rfl) ⟨1252709, by rfl⟩ : syracuseStep 1670279 = 2505419) B2505419
theorem B2505863 : Blo 1670035 2505863 := bstep (se 1 (by rfl) ⟨1879397, by rfl⟩ : syracuseStep 2505863 = 3758795) B3758795
theorem B1670287 : Blo 1670035 1670287 := bstep (se 1 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 1670287 = 2505431) B2505431
theorem B2505899 : Blo 1670035 2505899 := bstep (se 1 (by rfl) ⟨1879424, by rfl⟩ : syracuseStep 2505899 = 3758849) B3758849
theorem B12696749 : Blo 1670035 12696749 := bstep (se 3 (by rfl) ⟨2380640, by rfl⟩ : syracuseStep 12696749 = 4761281) B4761281
theorem B1670331 : Blo 1670035 1670331 := bstep (se 1 (by rfl) ⟨1252748, by rfl⟩ : syracuseStep 1670331 = 2505497) B2505497
theorem B2505929 : Blo 1670035 2505929 := bstep (se 2 (by rfl) ⟨939723, by rfl⟩ : syracuseStep 2505929 = 1879447) B1879447
theorem B6020333 : Blo 1670035 6020333 := bstep (se 3 (by rfl) ⟨1128812, by rfl⟩ : syracuseStep 6020333 = 2257625) B2257625
theorem B1670407 : Blo 1670035 1670407 := bstep (se 1 (by rfl) ⟨1252805, by rfl⟩ : syracuseStep 1670407 = 2505611) B2505611
theorem B1670415 : Blo 1670035 1670415 := bstep (se 1 (by rfl) ⟨1252811, by rfl⟩ : syracuseStep 1670415 = 2505623) B2505623
theorem B8461583 : Blo 1670035 8461583 := bstep (se 1 (by rfl) ⟨6346187, by rfl⟩ : syracuseStep 8461583 = 12692375) B12692375
theorem B1670459 : Blo 1670035 1670459 := bstep (se 1 (by rfl) ⟨1252844, by rfl⟩ : syracuseStep 1670459 = 2505689) B2505689
theorem B2506043 : Blo 1670035 2506043 := bstep (se 1 (by rfl) ⟨1879532, by rfl⟩ : syracuseStep 2506043 = 3759065) B3759065
theorem B2506103 : Blo 1670035 2506103 := bstep (se 1 (by rfl) ⟨1879577, by rfl⟩ : syracuseStep 2506103 = 3759155) B3759155
theorem B3759479 : Blo 1670035 3759479 := bstep (se 1 (by rfl) ⟨2819609, by rfl⟩ : syracuseStep 3759479 = 5639219) B5639219
theorem B21405059 : Blo 1670035 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B1670535 : Blo 1670035 1670535 := bstep (se 1 (by rfl) ⟨1252901, by rfl⟩ : syracuseStep 1670535 = 2505803) B2505803
theorem B1670543 : Blo 1670035 1670543 := bstep (se 1 (by rfl) ⟨1252907, by rfl⟩ : syracuseStep 1670543 = 2505815) B2505815
theorem B2506127 : Blo 1670035 2506127 := bstep (se 1 (by rfl) ⟨1879595, by rfl⟩ : syracuseStep 2506127 = 3759191) B3759191
theorem B2506169 : Blo 1670035 2506169 := bstep (se 2 (by rfl) ⟨939813, by rfl⟩ : syracuseStep 2506169 = 1879627) B1879627
theorem B1670587 : Blo 1670035 1670587 := bstep (se 1 (by rfl) ⟨1252940, by rfl⟩ : syracuseStep 1670587 = 2505881) B2505881
theorem B1670663 : Blo 1670035 1670663 := bstep (se 1 (by rfl) ⟨1252997, by rfl⟩ : syracuseStep 1670663 = 2505995) B2505995
theorem B2506247 : Blo 1670035 2506247 := bstep (se 1 (by rfl) ⟨1879685, by rfl⟩ : syracuseStep 2506247 = 3759371) B3759371
theorem B1670671 : Blo 1670035 1670671 := bstep (se 1 (by rfl) ⟨1253003, by rfl⟩ : syracuseStep 1670671 = 2506007) B2506007
theorem B2506283 : Blo 1670035 2506283 := bstep (se 1 (by rfl) ⟨1879712, by rfl⟩ : syracuseStep 2506283 = 3759425) B3759425
theorem B3759659 : Blo 1670035 3759659 := bstep (se 1 (by rfl) ⟨2819744, by rfl⟩ : syracuseStep 3759659 = 5639489) B5639489
theorem B1670715 : Blo 1670035 1670715 := bstep (se 1 (by rfl) ⟨1253036, by rfl⟩ : syracuseStep 1670715 = 2506073) B2506073
theorem B2506313 : Blo 1670035 2506313 := bstep (se 2 (by rfl) ⟨939867, by rfl⟩ : syracuseStep 2506313 = 1879735) B1879735
theorem B12688973 : Blo 1670035 12688973 := bstep (se 3 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 12688973 = 4758365) B4758365
theorem B1670791 : Blo 1670035 1670791 := bstep (se 1 (by rfl) ⟨1253093, by rfl⟩ : syracuseStep 1670791 = 2506187) B2506187
theorem B4759175 : Blo 1670035 4759175 := bstep (se 1 (by rfl) ⟨3569381, by rfl⟩ : syracuseStep 4759175 = 7138763) B7138763
theorem B1670799 : Blo 1670035 1670799 := bstep (se 1 (by rfl) ⟨1253099, by rfl⟩ : syracuseStep 1670799 = 2506199) B2506199
theorem B1670843 : Blo 1670035 1670843 := bstep (se 1 (by rfl) ⟨1253132, by rfl⟩ : syracuseStep 1670843 = 2506265) B2506265
theorem B2506427 : Blo 1670035 2506427 := bstep (se 1 (by rfl) ⟨1879820, by rfl⟩ : syracuseStep 2506427 = 3759641) B3759641
theorem B13549285 : Blo 1670035 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B2506487 : Blo 1670035 2506487 := bstep (se 1 (by rfl) ⟨1879865, by rfl⟩ : syracuseStep 2506487 = 3759731) B3759731
theorem B1670919 : Blo 1670035 1670919 := bstep (se 1 (by rfl) ⟨1253189, by rfl⟩ : syracuseStep 1670919 = 2506379) B2506379
theorem B1670927 : Blo 1670035 1670927 := bstep (se 1 (by rfl) ⟨1253195, by rfl⟩ : syracuseStep 1670927 = 2506391) B2506391
theorem B2506511 : Blo 1670035 2506511 := bstep (se 1 (by rfl) ⟨1879883, by rfl⟩ : syracuseStep 2506511 = 3759767) B3759767
theorem B36134707 : Blo 1670035 36134707 := bstep (se 1 (by rfl) ⟨27101030, by rfl⟩ : syracuseStep 36134707 = 54202061) B54202061
theorem B2506553 : Blo 1670035 2506553 := bstep (se 2 (by rfl) ⟨939957, by rfl⟩ : syracuseStep 2506553 = 1879915) B1879915
theorem B1670971 : Blo 1670035 1670971 := bstep (se 1 (by rfl) ⟨1253228, by rfl⟩ : syracuseStep 1670971 = 2506457) B2506457
theorem B4759357 : Blo 1670035 4759357 := bstep (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) B1784759
theorem B1671047 : Blo 1670035 1671047 := bstep (se 1 (by rfl) ⟨1253285, by rfl⟩ : syracuseStep 1671047 = 2506571) B2506571
theorem B2506631 : Blo 1670035 2506631 := bstep (se 1 (by rfl) ⟨1879973, by rfl⟩ : syracuseStep 2506631 = 3759947) B3759947
theorem B3719047 : Blo 1670035 3719047 := bstep (se 1 (by rfl) ⟨2789285, by rfl⟩ : syracuseStep 3719047 = 5578571) B5578571
theorem B1671055 : Blo 1670035 1671055 := bstep (se 1 (by rfl) ⟨1253291, by rfl⟩ : syracuseStep 1671055 = 2506583) B2506583
theorem B3760019 : Blo 1670035 3760019 := bstep (se 1 (by rfl) ⟨2820014, by rfl⟩ : syracuseStep 3760019 = 5640029) B5640029
theorem B2506667 : Blo 1670035 2506667 := bstep (se 1 (by rfl) ⟨1880000, by rfl⟩ : syracuseStep 2506667 = 3760001) B3760001
theorem B1671099 : Blo 1670035 1671099 := bstep (se 1 (by rfl) ⟨1253324, by rfl⟩ : syracuseStep 1671099 = 2506649) B2506649
theorem B2506697 : Blo 1670035 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B3760073 : Blo 1670035 3760073 := bstep (se 2 (by rfl) ⟨1410027, by rfl⟩ : syracuseStep 3760073 = 2820055) B2820055
theorem B1671207 : Blo 1670035 1671207 := bstep (se 1 (by rfl) ⟨1253405, by rfl⟩ : syracuseStep 1671207 = 2506811) B2506811
theorem B8462393 : Blo 1670035 8462393 := bstep (se 2 (by rfl) ⟨3173397, by rfl⟩ : syracuseStep 8462393 = 6346795) B6346795
theorem B1671247 : Blo 1670035 1671247 := bstep (se 1 (by rfl) ⟨1253435, by rfl⟩ : syracuseStep 1671247 = 2506871) B2506871
theorem B4759631 : Blo 1670035 4759631 := bstep (se 1 (by rfl) ⟨3569723, by rfl⟩ : syracuseStep 4759631 = 7139447) B7139447
theorem B6430801 : Blo 1670035 6430801 := bstep (se 2 (by rfl) ⟨2411550, by rfl⟩ : syracuseStep 6430801 = 4823101) B4823101
theorem B1671263 : Blo 1670035 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B1671291 : Blo 1670035 1671291 := bstep (se 1 (by rfl) ⟨1253468, by rfl⟩ : syracuseStep 1671291 = 2506937) B2506937
theorem B2818219 : Blo 1670035 2818219 := bstep (se 1 (by rfl) ⟨2113664, by rfl⟩ : syracuseStep 2818219 = 4227329) B4227329
theorem B1671343 : Blo 1670035 1671343 := bstep (se 1 (by rfl) ⟨1253507, by rfl⟩ : syracuseStep 1671343 = 2507015) B2507015
theorem B2007239 : Blo 1670035 2007239 := bstep (se 1 (by rfl) ⟨1505429, by rfl⟩ : syracuseStep 2007239 = 3010859) B3010859
theorem B1671367 : Blo 1670035 1671367 := bstep (se 1 (by rfl) ⟨1253525, by rfl⟩ : syracuseStep 1671367 = 2507051) B2507051
theorem B1671387 : Blo 1670035 1671387 := bstep (se 1 (by rfl) ⟨1253540, by rfl⟩ : syracuseStep 1671387 = 2507081) B2507081
theorem B1671463 : Blo 1670035 1671463 := bstep (se 1 (by rfl) ⟨1253597, by rfl⟩ : syracuseStep 1671463 = 2507195) B2507195
theorem B1671503 : Blo 1670035 1671503 := bstep (se 1 (by rfl) ⟨1253627, by rfl⟩ : syracuseStep 1671503 = 2507255) B2507255
theorem B1671519 : Blo 1670035 1671519 := bstep (se 1 (by rfl) ⟨1253639, by rfl⟩ : syracuseStep 1671519 = 2507279) B2507279
theorem B2539883 : Blo 1670035 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B1671547 : Blo 1670035 1671547 := bstep (se 1 (by rfl) ⟨1253660, by rfl⟩ : syracuseStep 1671547 = 2507321) B2507321
theorem B2507183 : Blo 1670035 2507183 := bstep (se 1 (by rfl) ⟨1880387, by rfl⟩ : syracuseStep 2507183 = 3760775) B3760775
theorem B1671599 : Blo 1670035 1671599 := bstep (se 1 (by rfl) ⟨1253699, by rfl⟩ : syracuseStep 1671599 = 2507399) B2507399
theorem B1671623 : Blo 1670035 1671623 := bstep (se 1 (by rfl) ⟨1253717, by rfl⟩ : syracuseStep 1671623 = 2507435) B2507435
theorem B2818523 : Blo 1670035 2818523 := bstep (se 1 (by rfl) ⟨2113892, by rfl⟩ : syracuseStep 2818523 = 4227785) B4227785
theorem B1671643 : Blo 1670035 1671643 := bstep (se 1 (by rfl) ⟨1253732, by rfl⟩ : syracuseStep 1671643 = 2507465) B2507465
theorem B3760649 : Blo 1670035 3760649 := bstep (se 2 (by rfl) ⟨1410243, by rfl⟩ : syracuseStep 3760649 = 2820487) B2820487
theorem B2507273 : Blo 1670035 2507273 := bstep (se 2 (by rfl) ⟨940227, by rfl⟩ : syracuseStep 2507273 = 1880455) B1880455
theorem B7332377 : Blo 1670035 7332377 := bstep (se 2 (by rfl) ⟨2749641, by rfl⟩ : syracuseStep 7332377 = 5499283) B5499283
theorem B12689945 : Blo 1670035 12689945 := bstep (se 2 (by rfl) ⟨4758729, by rfl⟩ : syracuseStep 12689945 = 9517459) B9517459
theorem B4227623 : Blo 1670035 4227623 := bstep (se 1 (by rfl) ⟨3170717, by rfl⟩ : syracuseStep 4227623 = 6341435) B6341435
theorem B2507303 : Blo 1670035 2507303 := bstep (se 1 (by rfl) ⟨1880477, by rfl⟩ : syracuseStep 2507303 = 3760955) B3760955
theorem B1671719 : Blo 1670035 1671719 := bstep (se 1 (by rfl) ⟨1253789, by rfl⟩ : syracuseStep 1671719 = 2507579) B2507579
theorem B1671759 : Blo 1670035 1671759 := bstep (se 1 (by rfl) ⟨1253819, by rfl⟩ : syracuseStep 1671759 = 2507639) B2507639
theorem B1671775 : Blo 1670035 1671775 := bstep (se 1 (by rfl) ⟨1253831, by rfl⟩ : syracuseStep 1671775 = 2507663) B2507663
theorem B2507387 : Blo 1670035 2507387 := bstep (se 1 (by rfl) ⟨1880540, by rfl⟩ : syracuseStep 2507387 = 3761081) B3761081
theorem B1671803 : Blo 1670035 1671803 := bstep (se 1 (by rfl) ⟨1253852, by rfl⟩ : syracuseStep 1671803 = 2507705) B2507705
theorem B6341267 : Blo 1670035 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B1671855 : Blo 1670035 1671855 := bstep (se 1 (by rfl) ⟨1253891, by rfl⟩ : syracuseStep 1671855 = 2507783) B2507783
theorem B2818759 : Blo 1670035 2818759 := bstep (se 1 (by rfl) ⟨2114069, by rfl⟩ : syracuseStep 2818759 = 4228139) B4228139
theorem B1671879 : Blo 1670035 1671879 := bstep (se 1 (by rfl) ⟨1253909, by rfl⟩ : syracuseStep 1671879 = 2507819) B2507819
theorem B4760279 : Blo 1670035 4760279 := bstep (se 1 (by rfl) ⟨3570209, by rfl⟩ : syracuseStep 4760279 = 7140419) B7140419
theorem B1671899 : Blo 1670035 1671899 := bstep (se 1 (by rfl) ⟨1253924, by rfl⟩ : syracuseStep 1671899 = 2507849) B2507849
theorem B2507513 : Blo 1670035 2507513 := bstep (se 2 (by rfl) ⟨940317, by rfl⟩ : syracuseStep 2507513 = 1880635) B1880635
theorem B24421121 : Blo 1670035 24421121 := bstep (se 2 (by rfl) ⟨9157920, by rfl⟩ : syracuseStep 24421121 = 18315841) B18315841
theorem B9519875 : Blo 1670035 9519875 := bstep (se 1 (by rfl) ⟨7139906, by rfl⟩ : syracuseStep 9519875 = 14279813) B14279813
theorem B8454941 : Blo 1670035 8454941 := bstep (se 3 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 8454941 = 3170603) B3170603
theorem B1671975 : Blo 1670035 1671975 := bstep (se 1 (by rfl) ⟨1253981, by rfl⟩ : syracuseStep 1671975 = 2507963) B2507963
theorem B6341449 : Blo 1670035 6341449 := bstep (se 2 (by rfl) ⟨2378043, by rfl⟩ : syracuseStep 6341449 = 4756087) B4756087
theorem B1672015 : Blo 1670035 1672015 := bstep (se 1 (by rfl) ⟨1254011, by rfl⟩ : syracuseStep 1672015 = 2508023) B2508023
theorem B3760991 : Blo 1670035 3760991 := bstep (se 1 (by rfl) ⟨2820743, by rfl⟩ : syracuseStep 3760991 = 5641487) B5641487
theorem B2507615 : Blo 1670035 2507615 := bstep (se 1 (by rfl) ⟨1880711, by rfl⟩ : syracuseStep 2507615 = 3761423) B3761423
theorem B1672031 : Blo 1670035 1672031 := bstep (se 1 (by rfl) ⟨1254023, by rfl⟩ : syracuseStep 1672031 = 2508047) B2508047
theorem B2818921 : Blo 1670035 2818921 := bstep (se 2 (by rfl) ⟨1057095, by rfl⟩ : syracuseStep 2818921 = 2114191) B2114191
theorem B4227947 : Blo 1670035 4227947 := bstep (se 1 (by rfl) ⟨3170960, by rfl⟩ : syracuseStep 4227947 = 6341921) B6341921
theorem B2507627 : Blo 1670035 2507627 := bstep (se 1 (by rfl) ⟨1880720, by rfl⟩ : syracuseStep 2507627 = 3761441) B3761441
theorem B4760507 : Blo 1670035 4760507 := bstep (se 1 (by rfl) ⟨3570380, by rfl⟩ : syracuseStep 4760507 = 7140761) B7140761
theorem B3761171 : Blo 1670035 3761171 := bstep (se 1 (by rfl) ⟨2820878, by rfl⟩ : syracuseStep 3761171 = 5641757) B5641757
theorem B4760633 : Blo 1670035 4760633 := bstep (se 2 (by rfl) ⟨1785237, by rfl⟩ : syracuseStep 4760633 = 3570475) B3570475
theorem B2507855 : Blo 1670035 2507855 := bstep (se 1 (by rfl) ⟨1880891, by rfl⟩ : syracuseStep 2507855 = 3761783) B3761783
theorem B2507975 : Blo 1670035 2507975 := bstep (se 1 (by rfl) ⟨1880981, by rfl⟩ : syracuseStep 2507975 = 3761963) B3761963
theorem B21423305 : Blo 1670035 21423305 := bstep (se 2 (by rfl) ⟨8033739, by rfl⟩ : syracuseStep 21423305 = 16067479) B16067479
theorem B3171575 : Blo 1670035 3171575 := bstep (se 1 (by rfl) ⟨2378681, by rfl⟩ : syracuseStep 3171575 = 4757363) B4757363
theorem B9520375 : Blo 1670035 9520375 := bstep (se 1 (by rfl) ⟨7140281, by rfl⟩ : syracuseStep 9520375 = 14280563) B14280563
theorem B5637437 : Blo 1670035 5637437 := bstep (se 3 (by rfl) ⟨1057019, by rfl⟩ : syracuseStep 5637437 = 2114039) B2114039
theorem B3761513 : Blo 1670035 3761513 := bstep (se 2 (by rfl) ⟨1410567, by rfl⟩ : syracuseStep 3761513 = 2821135) B2821135
theorem B3171727 : Blo 1670035 3171727 := bstep (se 1 (by rfl) ⟨2378795, by rfl⟩ : syracuseStep 3171727 = 4757591) B4757591
theorem B2819515 : Blo 1670035 2819515 := bstep (se 1 (by rfl) ⟨2114636, by rfl⟩ : syracuseStep 2819515 = 4229273) B4229273
theorem B4228595 : Blo 1670035 4228595 := bstep (se 1 (by rfl) ⟨3171446, by rfl⟩ : syracuseStep 4228595 = 6342893) B6342893
theorem B2819623 : Blo 1670035 2819623 := bstep (se 1 (by rfl) ⟨2114717, by rfl⟩ : syracuseStep 2819623 = 4229435) B4229435
theorem B5351035 : Blo 1670035 5351035 := bstep (se 1 (by rfl) ⟨4013276, by rfl⟩ : syracuseStep 5351035 = 8026553) B8026553
theorem B5351111 : Blo 1670035 5351111 := bstep (se 1 (by rfl) ⟨4013333, by rfl⟩ : syracuseStep 5351111 = 8026667) B8026667
theorem B4228807 : Blo 1670035 4228807 := bstep (se 1 (by rfl) ⟨3171605, by rfl⟩ : syracuseStep 4228807 = 6343211) B6343211
theorem B2819947 : Blo 1670035 2819947 := bstep (se 1 (by rfl) ⟨2114960, by rfl⟩ : syracuseStep 2819947 = 4229921) B4229921
theorem B9029569 : Blo 1670035 9029569 := bstep (se 2 (by rfl) ⟨3386088, by rfl⟩ : syracuseStep 9029569 = 6772177) B6772177
theorem B13551623 : Blo 1670035 13551623 := bstep (se 1 (by rfl) ⟨10163717, by rfl⟩ : syracuseStep 13551623 = 20327435) B20327435
theorem B8464499 : Blo 1670035 8464499 := bstep (se 1 (by rfl) ⟨6348374, by rfl⟩ : syracuseStep 8464499 = 12696749) B12696749
theorem B5638301 : Blo 1670035 5638301 := bstep (se 3 (by rfl) ⟨1057181, by rfl⟩ : syracuseStep 5638301 = 2114363) B2114363
theorem B3172601 : Blo 1670035 3172601 := bstep (se 2 (by rfl) ⟨1189725, by rfl⟩ : syracuseStep 3172601 = 2379451) B2379451
theorem B11913473 : Blo 1670035 11913473 := bstep (se 2 (by rfl) ⟨4467552, by rfl⟩ : syracuseStep 11913473 = 8935105) B8935105
theorem B18065713 : Blo 1670035 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B65095987 : Blo 1670035 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B2378089 : Blo 1670035 2378089 := bstep (se 2 (by rfl) ⟨891783, by rfl⟩ : syracuseStep 2378089 = 1783567) B1783567
theorem B48179609 : Blo 1670035 48179609 := bstep (se 2 (by rfl) ⟨18067353, by rfl⟩ : syracuseStep 48179609 = 36134707) B36134707
theorem B3172783 : Blo 1670035 3172783 := bstep (se 1 (by rfl) ⟨2379587, by rfl⟩ : syracuseStep 3172783 = 4759175) B4759175
theorem B4958729 : Blo 1670035 4958729 := bstep (se 2 (by rfl) ⟨1859523, by rfl⟩ : syracuseStep 4958729 = 3719047) B3719047
theorem B2116135 : Blo 1670035 2116135 := bstep (se 1 (by rfl) ⟨1587101, by rfl⟩ : syracuseStep 2116135 = 3174203) B3174203
theorem B4229729 : Blo 1670035 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B9030329 : Blo 1670035 9030329 := bstep (se 2 (by rfl) ⟨3386373, by rfl⟩ : syracuseStep 9030329 = 6772747) B6772747
theorem B5638841 : Blo 1670035 5638841 := bstep (se 2 (by rfl) ⟨2114565, by rfl⟩ : syracuseStep 5638841 = 4229131) B4229131
theorem B109939393 : Blo 1670035 109939393 := bstep (se 2 (by rfl) ⟨41227272, by rfl⟩ : syracuseStep 109939393 = 82454545) B82454545
theorem B6343379 : Blo 1670035 6343379 := bstep (se 1 (by rfl) ⟨4757534, by rfl⟩ : syracuseStep 6343379 = 9515069) B9515069
theorem B2821007 : Blo 1670035 2821007 := bstep (se 1 (by rfl) ⟨2115755, by rfl⟩ : syracuseStep 2821007 = 4231511) B4231511
theorem B325241891 : Blo 1670035 325241891 := bstep (se 1 (by rfl) ⟨243931418, by rfl⟩ : syracuseStep 325241891 = 487862837) B487862837
theorem B2821243 : Blo 1670035 2821243 := bstep (se 1 (by rfl) ⟨2115932, by rfl⟩ : syracuseStep 2821243 = 4231865) B4231865
theorem B14273729 : Blo 1670035 14273729 := bstep (se 2 (by rfl) ⟨5352648, by rfl⟩ : syracuseStep 14273729 = 10705297) B10705297
theorem B21417155 : Blo 1670035 21417155 := bstep (se 1 (by rfl) ⟨16062866, by rfl⟩ : syracuseStep 21417155 = 32125733) B32125733
theorem B5639435 : Blo 1670035 5639435 := bstep (se 1 (by rfl) ⟨4229576, by rfl⟩ : syracuseStep 5639435 = 8459153) B8459153
theorem B13544741 : Blo 1670035 13544741 := bstep (se 4 (by rfl) ⟨1269819, by rfl⟩ : syracuseStep 13544741 = 2539639) B2539639
theorem B12692861 : Blo 1670035 12692861 := bstep (se 3 (by rfl) ⟨2379911, by rfl⟩ : syracuseStep 12692861 = 4759823) B4759823
theorem B5352905 : Blo 1670035 5352905 := bstep (se 2 (by rfl) ⟨2007339, by rfl⟩ : syracuseStep 5352905 = 4014679) B4014679
theorem B5639705 : Blo 1670035 5639705 := bstep (se 2 (by rfl) ⟨2114889, by rfl⟩ : syracuseStep 5639705 = 4229779) B4229779
theorem B1879591 : Blo 1670035 1879591 := bstep (se 1 (by rfl) ⟨1409693, by rfl⟩ : syracuseStep 1879591 = 2819387) B2819387
theorem B3174059 : Blo 1670035 3174059 := bstep (se 1 (by rfl) ⟨2380544, by rfl⟩ : syracuseStep 3174059 = 4761089) B4761089
theorem B14282477 : Blo 1670035 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B48172913 : Blo 1670035 48172913 := bstep (se 2 (by rfl) ⟨18064842, by rfl⟩ : syracuseStep 48172913 = 36129685) B36129685
theorem B6434747 : Blo 1670035 6434747 := bstep (se 1 (by rfl) ⟨4826060, by rfl⟩ : syracuseStep 6434747 = 9652121) B9652121
theorem B4231187 : Blo 1670035 4231187 := bstep (se 1 (by rfl) ⟨3173390, by rfl⟩ : syracuseStep 4231187 = 6346781) B6346781
theorem B19034189 : Blo 1670035 19034189 := bstep (se 3 (by rfl) ⟨3568910, by rfl⟩ : syracuseStep 19034189 = 7137821) B7137821
theorem B2748745 : Blo 1670035 2748745 := bstep (se 2 (by rfl) ⟨1030779, by rfl⟩ : syracuseStep 2748745 = 2061559) B2061559
theorem B9515501 : Blo 1670035 9515501 := bstep (se 3 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 9515501 = 3568313) B3568313
theorem B6025709 : Blo 1670035 6025709 := bstep (se 3 (by rfl) ⟨1129820, by rfl⟩ : syracuseStep 6025709 = 2259641) B2259641
theorem B24080921 : Blo 1670035 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B5354009 : Blo 1670035 5354009 := bstep (se 2 (by rfl) ⟨2007753, by rfl⟩ : syracuseStep 5354009 = 4015507) B4015507
theorem B20328985 : Blo 1670035 20328985 := bstep (se 2 (by rfl) ⟨7623369, by rfl⟩ : syracuseStep 20328985 = 15246739) B15246739
theorem B5640839 : Blo 1670035 5640839 := bstep (se 1 (by rfl) ⟨4230629, by rfl⟩ : syracuseStep 5640839 = 8461259) B8461259
theorem B5640893 : Blo 1670035 5640893 := bstep (se 3 (by rfl) ⟨1057667, by rfl⟩ : syracuseStep 5640893 = 2115335) B2115335
theorem B5641055 : Blo 1670035 5641055 := bstep (se 1 (by rfl) ⟨4230791, by rfl⟩ : syracuseStep 5641055 = 8461583) B8461583
theorem B5641217 : Blo 1670035 5641217 := bstep (se 2 (by rfl) ⟨2115456, by rfl⟩ : syracuseStep 5641217 = 4230913) B4230913
theorem B14267441 : Blo 1670035 14267441 := bstep (se 2 (by rfl) ⟨5350290, by rfl⟩ : syracuseStep 14267441 = 10700581) B10700581
theorem B8459315 : Blo 1670035 8459315 := bstep (se 1 (by rfl) ⟨6344486, by rfl⟩ : syracuseStep 8459315 = 12688973) B12688973
theorem B6345809 : Blo 1670035 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B4068713 : Blo 1670035 4068713 := bstep (se 2 (by rfl) ⟨1525767, by rfl⟩ : syracuseStep 4068713 = 3051535) B3051535
theorem B6346127 : Blo 1670035 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B12547493 : Blo 1670035 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B3757607 : Blo 1670035 3757607 := bstep (se 1 (by rfl) ⟨2818205, by rfl⟩ : syracuseStep 3757607 = 5636411) B5636411
theorem B42817085 : Blo 1670035 42817085 := bstep (se 3 (by rfl) ⟨8028203, by rfl⟩ : syracuseStep 42817085 = 16056407) B16056407
theorem B27088577 : Blo 1670035 27088577 := bstep (se 2 (by rfl) ⟨10158216, by rfl⟩ : syracuseStep 27088577 = 20316433) B20316433
theorem B1783495 : Blo 1670035 1783495 := bstep (se 1 (by rfl) ⟨1337621, by rfl⟩ : syracuseStep 1783495 = 2675243) B2675243
theorem B2676473 : Blo 1670035 2676473 := bstep (se 2 (by rfl) ⟨1003677, by rfl⟩ : syracuseStep 2676473 = 2007355) B2007355
theorem B5642027 : Blo 1670035 5642027 := bstep (se 1 (by rfl) ⟨4231520, by rfl⟩ : syracuseStep 5642027 = 8463041) B8463041
theorem B10852163 : Blo 1670035 10852163 := bstep (se 1 (by rfl) ⟨8139122, by rfl⟩ : syracuseStep 10852163 = 16278245) B16278245
theorem B3757931 : Blo 1670035 3757931 := bstep (se 1 (by rfl) ⟨2818448, by rfl⟩ : syracuseStep 3757931 = 5636897) B5636897
theorem B30496621 : Blo 1670035 30496621 := bstep (se 3 (by rfl) ⟨5718116, by rfl⟩ : syracuseStep 30496621 = 11436233) B11436233
theorem B3757985 : Blo 1670035 3757985 := bstep (se 2 (by rfl) ⟨1409244, by rfl⟩ : syracuseStep 3757985 = 2818489) B2818489
theorem B18061217 : Blo 1670035 18061217 := bstep (se 2 (by rfl) ⟨6772956, by rfl⟩ : syracuseStep 18061217 = 13545913) B13545913
theorem B8034241 : Blo 1670035 8034241 := bstep (se 2 (by rfl) ⟨3012840, by rfl⟩ : syracuseStep 8034241 = 6025681) B6025681
theorem B5642297 : Blo 1670035 5642297 := bstep (se 2 (by rfl) ⟨2115861, by rfl⟩ : syracuseStep 5642297 = 4231723) B4231723
theorem B3758327 : Blo 1670035 3758327 := bstep (se 1 (by rfl) ⟨2818745, by rfl⟩ : syracuseStep 3758327 = 5637491) B5637491
theorem B6347069 : Blo 1670035 6347069 := bstep (se 3 (by rfl) ⟨1190075, by rfl⟩ : syracuseStep 6347069 = 2380151) B2380151
theorem B2259295 : Blo 1670035 2259295 := bstep (se 1 (by rfl) ⟨1694471, by rfl⟩ : syracuseStep 2259295 = 3388943) B3388943
theorem B2505065 : Blo 1670035 2505065 := bstep (se 2 (by rfl) ⟨939399, by rfl⟩ : syracuseStep 2505065 = 1878799) B1878799
theorem B5642621 : Blo 1670035 5642621 := bstep (se 3 (by rfl) ⟨1057991, by rfl⟩ : syracuseStep 5642621 = 2115983) B2115983
theorem B19028357 : Blo 1670035 19028357 := bstep (se 4 (by rfl) ⟨1783908, by rfl⟩ : syracuseStep 19028357 = 3567817) B3567817
theorem B2505143 : Blo 1670035 2505143 := bstep (se 1 (by rfl) ⟨1878857, by rfl⟩ : syracuseStep 2505143 = 3757715) B3757715
theorem B3013051 : Blo 1670035 3013051 := bstep (se 1 (by rfl) ⟨2259788, by rfl⟩ : syracuseStep 3013051 = 4519577) B4519577
theorem B2505179 : Blo 1670035 2505179 := bstep (se 1 (by rfl) ⟨1878884, by rfl⟩ : syracuseStep 2505179 = 3757769) B3757769
theorem B24099373 : Blo 1670035 24099373 := bstep (se 3 (by rfl) ⟨4518632, by rfl⟩ : syracuseStep 24099373 = 9037265) B9037265
theorem B8460935 : Blo 1670035 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B5642891 : Blo 1670035 5642891 := bstep (se 1 (by rfl) ⟨4232168, by rfl⟩ : syracuseStep 5642891 = 8464337) B8464337
theorem B6019769 : Blo 1670035 6019769 := bstep (se 2 (by rfl) ⟨2257413, by rfl⟩ : syracuseStep 6019769 = 4514827) B4514827
theorem B9779921 : Blo 1670035 9779921 := bstep (se 2 (by rfl) ⟨3667470, by rfl⟩ : syracuseStep 9779921 = 7334941) B7334941
theorem B3758921 : Blo 1670035 3758921 := bstep (se 2 (by rfl) ⟨1409595, by rfl⟩ : syracuseStep 3758921 = 2819191) B2819191
theorem B1670063 : Blo 1670035 1670063 := bstep (se 1 (by rfl) ⟨1252547, by rfl⟩ : syracuseStep 1670063 = 2505095) B2505095
theorem B2505647 : Blo 1670035 2505647 := bstep (se 1 (by rfl) ⟨1879235, by rfl⟩ : syracuseStep 2505647 = 3758471) B3758471
theorem B1670087 : Blo 1670035 1670087 := bstep (se 1 (by rfl) ⟨1252565, by rfl⟩ : syracuseStep 1670087 = 2505131) B2505131
theorem B1670107 : Blo 1670035 1670107 := bstep (se 1 (by rfl) ⟨1252580, by rfl⟩ : syracuseStep 1670107 = 2505161) B2505161
theorem B2505737 : Blo 1670035 2505737 := bstep (se 2 (by rfl) ⟨939651, by rfl⟩ : syracuseStep 2505737 = 1879303) B1879303
theorem B1670183 : Blo 1670035 1670183 := bstep (se 1 (by rfl) ⟨1252637, by rfl⟩ : syracuseStep 1670183 = 2505275) B2505275
theorem B2505767 : Blo 1670035 2505767 := bstep (se 1 (by rfl) ⟨1879325, by rfl⟩ : syracuseStep 2505767 = 3758651) B3758651
theorem B1670223 : Blo 1670035 1670223 := bstep (se 1 (by rfl) ⟨1252667, by rfl⟩ : syracuseStep 1670223 = 2505335) B2505335
theorem B28941391 : Blo 1670035 28941391 := bstep (se 1 (by rfl) ⟨21706043, by rfl⟩ : syracuseStep 28941391 = 43412087) B43412087
theorem B1670239 : Blo 1670035 1670239 := bstep (se 1 (by rfl) ⟨1252679, by rfl⟩ : syracuseStep 1670239 = 2505359) B2505359
theorem B1670267 : Blo 1670035 1670267 := bstep (se 1 (by rfl) ⟨1252700, by rfl⟩ : syracuseStep 1670267 = 2505401) B2505401
theorem B2505851 : Blo 1670035 2505851 := bstep (se 1 (by rfl) ⟨1879388, by rfl⟩ : syracuseStep 2505851 = 3758777) B3758777
theorem B1670319 : Blo 1670035 1670319 := bstep (se 1 (by rfl) ⟨1252739, by rfl⟩ : syracuseStep 1670319 = 2505479) B2505479
theorem B1670343 : Blo 1670035 1670343 := bstep (se 1 (by rfl) ⟨1252757, by rfl⟩ : syracuseStep 1670343 = 2505515) B2505515
theorem B1670363 : Blo 1670035 1670363 := bstep (se 1 (by rfl) ⟨1252772, by rfl⟩ : syracuseStep 1670363 = 2505545) B2505545
theorem B2505977 : Blo 1670035 2505977 := bstep (se 2 (by rfl) ⟨939741, by rfl⟩ : syracuseStep 2505977 = 1879483) B1879483
theorem B1670439 : Blo 1670035 1670439 := bstep (se 1 (by rfl) ⟨1252829, by rfl⟩ : syracuseStep 1670439 = 2505659) B2505659
theorem B1670479 : Blo 1670035 1670479 := bstep (se 1 (by rfl) ⟨1252859, by rfl⟩ : syracuseStep 1670479 = 2505719) B2505719
theorem B21708121 : Blo 1670035 21708121 := bstep (se 2 (by rfl) ⟨8140545, by rfl⟩ : syracuseStep 21708121 = 16281091) B16281091
theorem B1670495 : Blo 1670035 1670495 := bstep (se 1 (by rfl) ⟨1252871, by rfl⟩ : syracuseStep 1670495 = 2505743) B2505743
theorem B2506079 : Blo 1670035 2506079 := bstep (se 1 (by rfl) ⟨1879559, by rfl⟩ : syracuseStep 2506079 = 3759119) B3759119
theorem B2506091 : Blo 1670035 2506091 := bstep (se 1 (by rfl) ⟨1879568, by rfl⟩ : syracuseStep 2506091 = 3759137) B3759137
theorem B1670523 : Blo 1670035 1670523 := bstep (se 1 (by rfl) ⟨1252892, by rfl⟩ : syracuseStep 1670523 = 2505785) B2505785
theorem B12041615 : Blo 1670035 12041615 := bstep (se 1 (by rfl) ⟨9031211, by rfl⟩ : syracuseStep 12041615 = 18062423) B18062423
theorem B1670575 : Blo 1670035 1670575 := bstep (se 1 (by rfl) ⟨1252931, by rfl⟩ : syracuseStep 1670575 = 2505863) B2505863
theorem B1670599 : Blo 1670035 1670599 := bstep (se 1 (by rfl) ⟨1252949, by rfl⟩ : syracuseStep 1670599 = 2505899) B2505899
theorem B1670619 : Blo 1670035 1670619 := bstep (se 1 (by rfl) ⟨1252964, by rfl⟩ : syracuseStep 1670619 = 2505929) B2505929
theorem B4759003 : Blo 1670035 4759003 := bstep (se 1 (by rfl) ⟨3569252, by rfl⟩ : syracuseStep 4759003 = 7138505) B7138505
theorem B4013555 : Blo 1670035 4013555 := bstep (se 1 (by rfl) ⟨3010166, by rfl⟩ : syracuseStep 4013555 = 6020333) B6020333
theorem B4759049 : Blo 1670035 4759049 := bstep (se 2 (by rfl) ⟨1784643, by rfl⟩ : syracuseStep 4759049 = 3569287) B3569287
theorem B1670695 : Blo 1670035 1670695 := bstep (se 1 (by rfl) ⟨1253021, by rfl⟩ : syracuseStep 1670695 = 2506043) B2506043
theorem B1670735 : Blo 1670035 1670735 := bstep (se 1 (by rfl) ⟨1253051, by rfl⟩ : syracuseStep 1670735 = 2506103) B2506103
theorem B2506319 : Blo 1670035 2506319 := bstep (se 1 (by rfl) ⟨1879739, by rfl⟩ : syracuseStep 2506319 = 3759479) B3759479
theorem B14270039 : Blo 1670035 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B1670751 : Blo 1670035 1670751 := bstep (se 1 (by rfl) ⟨1253063, by rfl⟩ : syracuseStep 1670751 = 2506127) B2506127
theorem B13549153 : Blo 1670035 13549153 := bstep (se 2 (by rfl) ⟨5080932, by rfl⟩ : syracuseStep 13549153 = 10161865) B10161865
theorem B3759713 : Blo 1670035 3759713 := bstep (se 2 (by rfl) ⟨1409892, by rfl⟩ : syracuseStep 3759713 = 2819785) B2819785
theorem B1670779 : Blo 1670035 1670779 := bstep (se 1 (by rfl) ⟨1253084, by rfl⟩ : syracuseStep 1670779 = 2506169) B2506169
theorem B1670831 : Blo 1670035 1670831 := bstep (se 1 (by rfl) ⟨1253123, by rfl⟩ : syracuseStep 1670831 = 2506247) B2506247
theorem B1670855 : Blo 1670035 1670855 := bstep (se 1 (by rfl) ⟨1253141, by rfl⟩ : syracuseStep 1670855 = 2506283) B2506283
theorem B2506439 : Blo 1670035 2506439 := bstep (se 1 (by rfl) ⟨1879829, by rfl⟩ : syracuseStep 2506439 = 3759659) B3759659
theorem B4824791 : Blo 1670035 4824791 := bstep (se 1 (by rfl) ⟨3618593, by rfl⟩ : syracuseStep 4824791 = 7237187) B7237187
theorem B1670875 : Blo 1670035 1670875 := bstep (se 1 (by rfl) ⟨1253156, by rfl⟩ : syracuseStep 1670875 = 2506313) B2506313
theorem B1670951 : Blo 1670035 1670951 := bstep (se 1 (by rfl) ⟨1253213, by rfl⟩ : syracuseStep 1670951 = 2506427) B2506427
theorem B1670991 : Blo 1670035 1670991 := bstep (se 1 (by rfl) ⟨1253243, by rfl⟩ : syracuseStep 1670991 = 2506487) B2506487
theorem B1671007 : Blo 1670035 1671007 := bstep (se 1 (by rfl) ⟨1253255, by rfl⟩ : syracuseStep 1671007 = 2506511) B2506511
theorem B4759391 : Blo 1670035 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B2506601 : Blo 1670035 2506601 := bstep (se 2 (by rfl) ⟨939975, by rfl⟩ : syracuseStep 2506601 = 1879951) B1879951
theorem B1671035 : Blo 1670035 1671035 := bstep (se 1 (by rfl) ⟨1253276, by rfl⟩ : syracuseStep 1671035 = 2506553) B2506553
theorem B1671087 : Blo 1670035 1671087 := bstep (se 1 (by rfl) ⟨1253315, by rfl⟩ : syracuseStep 1671087 = 2506631) B2506631
theorem B2506679 : Blo 1670035 2506679 := bstep (se 1 (by rfl) ⟨1880009, by rfl⟩ : syracuseStep 2506679 = 3760019) B3760019
theorem B3760055 : Blo 1670035 3760055 := bstep (se 1 (by rfl) ⟨2820041, by rfl⟩ : syracuseStep 3760055 = 5640083) B5640083
theorem B1671111 : Blo 1670035 1671111 := bstep (se 1 (by rfl) ⟨1253333, by rfl⟩ : syracuseStep 1671111 = 2506667) B2506667
theorem B1671131 : Blo 1670035 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B2506715 : Blo 1670035 2506715 := bstep (se 1 (by rfl) ⟨1880036, by rfl⟩ : syracuseStep 2506715 = 3760073) B3760073
theorem B12689459 : Blo 1670035 12689459 := bstep (se 1 (by rfl) ⟨9517094, by rfl⟩ : syracuseStep 12689459 = 19034189) B19034189
theorem B1671455 : Blo 1670035 1671455 := bstep (se 1 (by rfl) ⟨1253591, by rfl⟩ : syracuseStep 1671455 = 2507183) B2507183
theorem B2507099 : Blo 1670035 2507099 := bstep (se 1 (by rfl) ⟨1880324, by rfl⟩ : syracuseStep 2507099 = 3760649) B3760649
theorem B1671515 : Blo 1670035 1671515 := bstep (se 1 (by rfl) ⟨1253636, by rfl⟩ : syracuseStep 1671515 = 2507273) B2507273
theorem B2818415 : Blo 1670035 2818415 := bstep (se 1 (by rfl) ⟨2113811, by rfl⟩ : syracuseStep 2818415 = 4227623) B4227623
theorem B1671535 : Blo 1670035 1671535 := bstep (se 1 (by rfl) ⟨1253651, by rfl⟩ : syracuseStep 1671535 = 2507303) B2507303
theorem B86794649 : Blo 1670035 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B1671591 : Blo 1670035 1671591 := bstep (se 1 (by rfl) ⟨1253693, by rfl⟩ : syracuseStep 1671591 = 2507387) B2507387
theorem B3760559 : Blo 1670035 3760559 := bstep (se 1 (by rfl) ⟨2820419, by rfl⟩ : syracuseStep 3760559 = 5640839) B5640839
theorem B4227511 : Blo 1670035 4227511 := bstep (se 1 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 4227511 = 6341267) B6341267
theorem B3760595 : Blo 1670035 3760595 := bstep (se 1 (by rfl) ⟨2820446, by rfl⟩ : syracuseStep 3760595 = 5640893) B5640893
theorem B1671675 : Blo 1670035 1671675 := bstep (se 1 (by rfl) ⟨1253756, by rfl⟩ : syracuseStep 1671675 = 2507513) B2507513
theorem B5636627 : Blo 1670035 5636627 := bstep (se 1 (by rfl) ⟨4227470, by rfl⟩ : syracuseStep 5636627 = 8454941) B8454941
theorem B3760703 : Blo 1670035 3760703 := bstep (se 1 (by rfl) ⟨2820527, by rfl⟩ : syracuseStep 3760703 = 5641055) B5641055
theorem B2507327 : Blo 1670035 2507327 := bstep (se 1 (by rfl) ⟨1880495, by rfl⟩ : syracuseStep 2507327 = 3760991) B3760991
theorem B1671743 : Blo 1670035 1671743 := bstep (se 1 (by rfl) ⟨1253807, by rfl⟩ : syracuseStep 1671743 = 2507615) B2507615
theorem B2818631 : Blo 1670035 2818631 := bstep (se 1 (by rfl) ⟨2113973, by rfl⟩ : syracuseStep 2818631 = 4227947) B4227947
theorem B1671751 : Blo 1670035 1671751 := bstep (se 1 (by rfl) ⟨1253813, by rfl⟩ : syracuseStep 1671751 = 2507627) B2507627
theorem B3760811 : Blo 1670035 3760811 := bstep (se 1 (by rfl) ⟨2820608, by rfl⟩ : syracuseStep 3760811 = 5641217) B5641217
theorem B2507447 : Blo 1670035 2507447 := bstep (se 1 (by rfl) ⟨1880585, by rfl⟩ : syracuseStep 2507447 = 3761171) B3761171
theorem B9511627 : Blo 1670035 9511627 := bstep (se 1 (by rfl) ⟨7133720, by rfl⟩ : syracuseStep 9511627 = 14267441) B14267441
theorem B1671903 : Blo 1670035 1671903 := bstep (se 1 (by rfl) ⟨1253927, by rfl⟩ : syracuseStep 1671903 = 2507855) B2507855
theorem B1671983 : Blo 1670035 1671983 := bstep (se 1 (by rfl) ⟨1253987, by rfl⟩ : syracuseStep 1671983 = 2507975) B2507975
theorem B2712475 : Blo 1670035 2712475 := bstep (se 1 (by rfl) ⟨2034356, by rfl⟩ : syracuseStep 2712475 = 4068713) B4068713
theorem B2507675 : Blo 1670035 2507675 := bstep (se 1 (by rfl) ⟨1880756, by rfl⟩ : syracuseStep 2507675 = 3761513) B3761513
theorem B8364995 : Blo 1670035 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B2819063 : Blo 1670035 2819063 := bstep (se 1 (by rfl) ⟨2114297, by rfl⟩ : syracuseStep 2819063 = 4228595) B4228595
theorem B8455265 : Blo 1670035 8455265 := bstep (se 2 (by rfl) ⟨3170724, by rfl⟩ : syracuseStep 8455265 = 6341449) B6341449
theorem B3761351 : Blo 1670035 3761351 := bstep (se 1 (by rfl) ⟨2821013, by rfl⟩ : syracuseStep 3761351 = 5642027) B5642027
theorem B7234775 : Blo 1670035 7234775 := bstep (se 1 (by rfl) ⟨5426081, by rfl⟩ : syracuseStep 7234775 = 10852163) B10852163
theorem B3761531 : Blo 1670035 3761531 := bstep (se 1 (by rfl) ⟨2821148, by rfl⟩ : syracuseStep 3761531 = 5642297) B5642297
theorem B3761657 : Blo 1670035 3761657 := bstep (se 2 (by rfl) ⟨1410621, by rfl⟩ : syracuseStep 3761657 = 2821243) B2821243
theorem B2115067 : Blo 1670035 2115067 := bstep (se 1 (by rfl) ⟨1586300, by rfl⟩ : syracuseStep 2115067 = 3172601) B3172601
theorem B3761747 : Blo 1670035 3761747 := bstep (se 1 (by rfl) ⟨2821310, by rfl⟩ : syracuseStep 3761747 = 5642621) B5642621
theorem B2819819 : Blo 1670035 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B3761927 : Blo 1670035 3761927 := bstep (se 1 (by rfl) ⟨2821445, by rfl⟩ : syracuseStep 3761927 = 5642891) B5642891
theorem B28944161 : Blo 1670035 28944161 := bstep (se 2 (by rfl) ⟨10854060, by rfl⟩ : syracuseStep 28944161 = 21708121) B21708121
theorem B4228919 : Blo 1670035 4228919 := bstep (se 1 (by rfl) ⟨3171689, by rfl⟩ : syracuseStep 4228919 = 6343379) B6343379
theorem B4228969 : Blo 1670035 4228969 := bstep (se 2 (by rfl) ⟨1585863, by rfl⟩ : syracuseStep 4228969 = 3171727) B3171727
theorem B12683141 : Blo 1670035 12683141 := bstep (se 4 (by rfl) ⟨1189044, by rfl⟩ : syracuseStep 12683141 = 2378089) B2378089
theorem B216827927 : Blo 1670035 216827927 := bstep (se 1 (by rfl) ⟨162620945, by rfl⟩ : syracuseStep 216827927 = 325241891) B325241891
theorem B18065537 : Blo 1670035 18065537 := bstep (se 2 (by rfl) ⟨6774576, by rfl⟩ : syracuseStep 18065537 = 13549153) B13549153
theorem B9029827 : Blo 1670035 9029827 := bstep (se 1 (by rfl) ⟨6772370, by rfl⟩ : syracuseStep 9029827 = 13544741) B13544741
theorem B2377993 : Blo 1670035 2377993 := bstep (se 2 (by rfl) ⟨891747, by rfl⟩ : syracuseStep 2377993 = 1783495) B1783495
theorem B5638409 : Blo 1670035 5638409 := bstep (se 2 (by rfl) ⟨2114403, by rfl⟩ : syracuseStep 5638409 = 4228807) B4228807
theorem B3172699 : Blo 1670035 3172699 := bstep (se 1 (by rfl) ⟨2379524, by rfl⟩ : syracuseStep 3172699 = 4759049) B4759049
theorem B9513359 : Blo 1670035 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B2116039 : Blo 1670035 2116039 := bstep (se 1 (by rfl) ⟨1587029, by rfl⟩ : syracuseStep 2116039 = 3174059) B3174059
theorem B9521651 : Blo 1670035 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B3172927 : Blo 1670035 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B32115275 : Blo 1670035 32115275 := bstep (se 1 (by rfl) ⟨24086456, by rfl⟩ : syracuseStep 32115275 = 48172913) B48172913
theorem B2820791 : Blo 1670035 2820791 := bstep (se 1 (by rfl) ⟨2115593, by rfl⟩ : syracuseStep 2820791 = 4231187) B4231187
theorem B3173087 : Blo 1670035 3173087 := bstep (se 1 (by rfl) ⟨2379815, by rfl⟩ : syracuseStep 3173087 = 4759631) B4759631
theorem B1879015 : Blo 1670035 1879015 := bstep (se 1 (by rfl) ⟨1409261, by rfl⟩ : syracuseStep 1879015 = 2818523) B2818523
theorem B6343667 : Blo 1670035 6343667 := bstep (se 1 (by rfl) ⟨4757750, by rfl⟩ : syracuseStep 6343667 = 9515501) B9515501
theorem B24087617 : Blo 1670035 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B3664993 : Blo 1670035 3664993 := bstep (se 2 (by rfl) ⟨1374372, by rfl⟩ : syracuseStep 3664993 = 2748745) B2748745
theorem B3173519 : Blo 1670035 3173519 := bstep (se 1 (by rfl) ⟨2380139, by rfl⟩ : syracuseStep 3173519 = 4760279) B4760279
theorem B16280747 : Blo 1670035 16280747 := bstep (se 1 (by rfl) ⟨12210560, by rfl⟩ : syracuseStep 16280747 = 24421121) B24421121
theorem B5352637 : Blo 1670035 5352637 := bstep (se 3 (by rfl) ⟨1003619, by rfl⟩ : syracuseStep 5352637 = 2007239) B2007239
theorem B4230377 : Blo 1670035 4230377 := bstep (se 2 (by rfl) ⟨1586391, by rfl⟩ : syracuseStep 4230377 = 3172783) B3172783
theorem B4017401 : Blo 1670035 4017401 := bstep (se 2 (by rfl) ⟨1506525, by rfl⟩ : syracuseStep 4017401 = 3013051) B3013051
theorem B3173671 : Blo 1670035 3173671 := bstep (se 1 (by rfl) ⟨2380253, by rfl⟩ : syracuseStep 3173671 = 4760507) B4760507
theorem B8457533 : Blo 1670035 8457533 := bstep (se 3 (by rfl) ⟨1585787, by rfl⟩ : syracuseStep 8457533 = 3171575) B3171575
theorem B5639543 : Blo 1670035 5639543 := bstep (se 1 (by rfl) ⟨4229657, by rfl⟩ : syracuseStep 5639543 = 8459315) B8459315
theorem B3173755 : Blo 1670035 3173755 := bstep (se 1 (by rfl) ⟨2380316, by rfl⟩ : syracuseStep 3173755 = 4760633) B4760633
theorem B2821513 : Blo 1670035 2821513 := bstep (se 2 (by rfl) ⟨1058067, by rfl⟩ : syracuseStep 2821513 = 2116135) B2116135
theorem B4230539 : Blo 1670035 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B32132497 : Blo 1670035 32132497 := bstep (se 2 (by rfl) ⟨12049686, by rfl⟩ : syracuseStep 32132497 = 24099373) B24099373
theorem B14282203 : Blo 1670035 14282203 := bstep (se 1 (by rfl) ⟨10711652, by rfl⟩ : syracuseStep 14282203 = 21423305) B21423305
theorem B4230751 : Blo 1670035 4230751 := bstep (se 1 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 4230751 = 6346127) B6346127
theorem B28544723 : Blo 1670035 28544723 := bstep (se 1 (by rfl) ⟨21408542, by rfl⟩ : syracuseStep 28544723 = 42817085) B42817085
theorem B18059051 : Blo 1670035 18059051 := bstep (se 1 (by rfl) ⟨13544288, by rfl⟩ : syracuseStep 18059051 = 27088577) B27088577
theorem B3567407 : Blo 1670035 3567407 := bstep (se 1 (by rfl) ⟨2675555, by rfl⟩ : syracuseStep 3567407 = 5351111) B5351111
theorem B14274413 : Blo 1670035 14274413 := bstep (se 3 (by rfl) ⟨2676452, by rfl⟩ : syracuseStep 14274413 = 5352905) B5352905
theorem B16068557 : Blo 1670035 16068557 := bstep (se 3 (by rfl) ⟨3012854, by rfl⟩ : syracuseStep 16068557 = 6025709) B6025709
theorem B10702813 : Blo 1670035 10702813 := bstep (se 3 (by rfl) ⟨2006777, by rfl⟩ : syracuseStep 10702813 = 4013555) B4013555
theorem B38588521 : Blo 1670035 38588521 := bstep (se 2 (by rfl) ⟨14470695, by rfl⟩ : syracuseStep 38588521 = 28941391) B28941391
theorem B7942315 : Blo 1670035 7942315 := bstep (se 1 (by rfl) ⟨5956736, by rfl⟩ : syracuseStep 7942315 = 11913473) B11913473
theorem B4231379 : Blo 1670035 4231379 := bstep (se 1 (by rfl) ⟨3173534, by rfl⟩ : syracuseStep 4231379 = 6347069) B6347069
theorem B12685571 : Blo 1670035 12685571 := bstep (se 1 (by rfl) ⟨9514178, by rfl⟩ : syracuseStep 12685571 = 19028357) B19028357
theorem B12693833 : Blo 1670035 12693833 := bstep (se 2 (by rfl) ⟨4760187, by rfl⟩ : syracuseStep 12693833 = 9520375) B9520375
theorem B3305819 : Blo 1670035 3305819 := bstep (se 1 (by rfl) ⟨2479364, by rfl⟩ : syracuseStep 3305819 = 4958729) B4958729
theorem B5640623 : Blo 1670035 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B16052717 : Blo 1670035 16052717 := bstep (se 3 (by rfl) ⟨3009884, by rfl⟩ : syracuseStep 16052717 = 6019769) B6019769
theorem B1880671 : Blo 1670035 1880671 := bstep (se 1 (by rfl) ⟨1410503, by rfl⟩ : syracuseStep 1880671 = 2821007) B2821007
theorem B6345337 : Blo 1670035 6345337 := bstep (se 2 (by rfl) ⟨2379501, by rfl⟩ : syracuseStep 6345337 = 4759003) B4759003
theorem B9515819 : Blo 1670035 9515819 := bstep (se 1 (by rfl) ⟨7136864, by rfl⟩ : syracuseStep 9515819 = 14273729) B14273729
theorem B3216527 : Blo 1670035 3216527 := bstep (se 1 (by rfl) ⟨2412395, by rfl⟩ : syracuseStep 3216527 = 4824791) B4824791
theorem B40662161 : Blo 1670035 40662161 := bstep (se 2 (by rfl) ⟨15248310, by rfl⟩ : syracuseStep 40662161 = 30496621) B30496621
theorem B12039425 : Blo 1670035 12039425 := bstep (se 2 (by rfl) ⟨4514784, by rfl⟩ : syracuseStep 12039425 = 9029569) B9029569
theorem B10712321 : Blo 1670035 10712321 := bstep (se 2 (by rfl) ⟨4017120, by rfl⟩ : syracuseStep 10712321 = 8034241) B8034241
theorem B4289831 : Blo 1670035 4289831 := bstep (se 1 (by rfl) ⟨3217373, by rfl⟩ : syracuseStep 4289831 = 6434747) B6434747
theorem B5641595 : Blo 1670035 5641595 := bstep (se 1 (by rfl) ⟨4231196, by rfl⟩ : syracuseStep 5641595 = 8462393) B8462393
theorem B8574401 : Blo 1670035 8574401 := bstep (se 2 (by rfl) ⟨3215400, by rfl⟩ : syracuseStep 8574401 = 6430801) B6430801
theorem B3757625 : Blo 1670035 3757625 := bstep (se 2 (by rfl) ⟨1409109, by rfl⟩ : syracuseStep 3757625 = 2818219) B2818219
theorem B16053947 : Blo 1670035 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B8459963 : Blo 1670035 8459963 := bstep (se 1 (by rfl) ⟨6344972, by rfl⟩ : syracuseStep 8459963 = 12689945) B12689945
theorem B3569339 : Blo 1670035 3569339 := bstep (se 1 (by rfl) ⟨2677004, by rfl⟩ : syracuseStep 3569339 = 5354009) B5354009
theorem B6346583 : Blo 1670035 6346583 := bstep (se 1 (by rfl) ⟨4759937, by rfl⟩ : syracuseStep 6346583 = 9519875) B9519875
theorem B27105313 : Blo 1670035 27105313 := bstep (se 2 (by rfl) ⟨10164492, by rfl⟩ : syracuseStep 27105313 = 20328985) B20328985
theorem B3758291 : Blo 1670035 3758291 := bstep (se 1 (by rfl) ⟨2818718, by rfl⟩ : syracuseStep 3758291 = 5637437) B5637437
theorem B146585857 : Blo 1670035 146585857 := bstep (se 2 (by rfl) ⟨54969696, by rfl⟩ : syracuseStep 146585857 = 109939393) B109939393
theorem B3758345 : Blo 1670035 3758345 := bstep (se 2 (by rfl) ⟨1409379, by rfl⟩ : syracuseStep 3758345 = 2818759) B2818759
theorem B6773021 : Blo 1670035 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B2505071 : Blo 1670035 2505071 := bstep (se 1 (by rfl) ⟨1878803, by rfl⟩ : syracuseStep 2505071 = 3757607) B3757607
theorem B3758561 : Blo 1670035 3758561 := bstep (se 2 (by rfl) ⟨1409460, by rfl⟩ : syracuseStep 3758561 = 2818921) B2818921
theorem B1784315 : Blo 1670035 1784315 := bstep (se 1 (by rfl) ⟨1338236, by rfl⟩ : syracuseStep 1784315 = 2676473) B2676473
theorem B2505287 : Blo 1670035 2505287 := bstep (se 1 (by rfl) ⟨1878965, by rfl⟩ : syracuseStep 2505287 = 3757931) B3757931
theorem B2505323 : Blo 1670035 2505323 := bstep (se 1 (by rfl) ⟨1878992, by rfl⟩ : syracuseStep 2505323 = 3757985) B3757985
theorem B12040811 : Blo 1670035 12040811 := bstep (se 1 (by rfl) ⟨9030608, by rfl⟩ : syracuseStep 12040811 = 18061217) B18061217
theorem B9034415 : Blo 1670035 9034415 := bstep (se 1 (by rfl) ⟨6775811, by rfl⟩ : syracuseStep 9034415 = 13551623) B13551623
theorem B19553005 : Blo 1670035 19553005 := bstep (se 3 (by rfl) ⟨3666188, by rfl⟩ : syracuseStep 19553005 = 7332377) B7332377
theorem B5642999 : Blo 1670035 5642999 := bstep (se 1 (by rfl) ⟨4232249, by rfl⟩ : syracuseStep 5642999 = 8464499) B8464499
theorem B3758867 : Blo 1670035 3758867 := bstep (se 1 (by rfl) ⟨2819150, by rfl⟩ : syracuseStep 3758867 = 5638301) B5638301
theorem B2505551 : Blo 1670035 2505551 := bstep (se 1 (by rfl) ⟨1879163, by rfl⟩ : syracuseStep 2505551 = 3758327) B3758327
theorem B1670043 : Blo 1670035 1670043 := bstep (se 1 (by rfl) ⟨1252532, by rfl⟩ : syracuseStep 1670043 = 2505065) B2505065
theorem B32119739 : Blo 1670035 32119739 := bstep (se 1 (by rfl) ⟨24089804, by rfl⟩ : syracuseStep 32119739 = 48179609) B48179609
theorem B1670095 : Blo 1670035 1670095 := bstep (se 1 (by rfl) ⟨1252571, by rfl⟩ : syracuseStep 1670095 = 2505143) B2505143
theorem B1670119 : Blo 1670035 1670119 := bstep (se 1 (by rfl) ⟨1252589, by rfl⟩ : syracuseStep 1670119 = 2505179) B2505179
theorem B6020219 : Blo 1670035 6020219 := bstep (se 1 (by rfl) ⟨4515164, by rfl⟩ : syracuseStep 6020219 = 9030329) B9030329
theorem B3759227 : Blo 1670035 3759227 := bstep (se 1 (by rfl) ⟨2819420, by rfl⟩ : syracuseStep 3759227 = 5638841) B5638841
theorem B6519947 : Blo 1670035 6519947 := bstep (se 1 (by rfl) ⟨4889960, by rfl⟩ : syracuseStep 6519947 = 9779921) B9779921
theorem B12049573 : Blo 1670035 12049573 := bstep (se 4 (by rfl) ⟨1129647, by rfl⟩ : syracuseStep 12049573 = 2259295) B2259295
theorem B2505947 : Blo 1670035 2505947 := bstep (se 1 (by rfl) ⟨1879460, by rfl⟩ : syracuseStep 2505947 = 3758921) B3758921
theorem B3759353 : Blo 1670035 3759353 := bstep (se 2 (by rfl) ⟨1409757, by rfl⟩ : syracuseStep 3759353 = 2819515) B2819515
theorem B1670431 : Blo 1670035 1670431 := bstep (se 1 (by rfl) ⟨1252823, by rfl⟩ : syracuseStep 1670431 = 2505647) B2505647
theorem B1670491 : Blo 1670035 1670491 := bstep (se 1 (by rfl) ⟨1252868, by rfl⟩ : syracuseStep 1670491 = 2505737) B2505737
theorem B1670511 : Blo 1670035 1670511 := bstep (se 1 (by rfl) ⟨1252883, by rfl⟩ : syracuseStep 1670511 = 2505767) B2505767
theorem B2506121 : Blo 1670035 2506121 := bstep (se 2 (by rfl) ⟨939795, by rfl⟩ : syracuseStep 2506121 = 1879591) B1879591
theorem B3759497 : Blo 1670035 3759497 := bstep (se 2 (by rfl) ⟨1409811, by rfl⟩ : syracuseStep 3759497 = 2819623) B2819623
theorem B1670567 : Blo 1670035 1670567 := bstep (se 1 (by rfl) ⟨1252925, by rfl⟩ : syracuseStep 1670567 = 2505851) B2505851
theorem B14278103 : Blo 1670035 14278103 := bstep (se 1 (by rfl) ⟨10708577, by rfl⟩ : syracuseStep 14278103 = 21417155) B21417155
theorem B7134713 : Blo 1670035 7134713 := bstep (se 2 (by rfl) ⟨2675517, by rfl⟩ : syracuseStep 7134713 = 5351035) B5351035
theorem B1670651 : Blo 1670035 1670651 := bstep (se 1 (by rfl) ⟨1252988, by rfl⟩ : syracuseStep 1670651 = 2505977) B2505977
theorem B3759623 : Blo 1670035 3759623 := bstep (se 1 (by rfl) ⟨2819717, by rfl⟩ : syracuseStep 3759623 = 5639435) B5639435
theorem B1670719 : Blo 1670035 1670719 := bstep (se 1 (by rfl) ⟨1253039, by rfl⟩ : syracuseStep 1670719 = 2506079) B2506079
theorem B1670727 : Blo 1670035 1670727 := bstep (se 1 (by rfl) ⟨1253045, by rfl⟩ : syracuseStep 1670727 = 2506091) B2506091
theorem B8461907 : Blo 1670035 8461907 := bstep (se 1 (by rfl) ⟨6346430, by rfl⟩ : syracuseStep 8461907 = 12692861) B12692861
theorem B8027743 : Blo 1670035 8027743 := bstep (se 1 (by rfl) ⟨6020807, by rfl⟩ : syracuseStep 8027743 = 12041615) B12041615
theorem B3759803 : Blo 1670035 3759803 := bstep (se 1 (by rfl) ⟨2819852, by rfl⟩ : syracuseStep 3759803 = 5639705) B5639705
theorem B1670879 : Blo 1670035 1670879 := bstep (se 1 (by rfl) ⟨1253159, by rfl⟩ : syracuseStep 1670879 = 2506319) B2506319
theorem B2506475 : Blo 1670035 2506475 := bstep (se 1 (by rfl) ⟨1879856, by rfl⟩ : syracuseStep 2506475 = 3759713) B3759713
theorem B1670959 : Blo 1670035 1670959 := bstep (se 1 (by rfl) ⟨1253219, by rfl⟩ : syracuseStep 1670959 = 2506439) B2506439
theorem B3759929 : Blo 1670035 3759929 := bstep (se 2 (by rfl) ⟨1409973, by rfl⟩ : syracuseStep 3759929 = 2819947) B2819947
theorem B1671067 : Blo 1670035 1671067 := bstep (se 1 (by rfl) ⟨1253300, by rfl⟩ : syracuseStep 1671067 = 2506601) B2506601
theorem B1671119 : Blo 1670035 1671119 := bstep (se 1 (by rfl) ⟨1253339, by rfl⟩ : syracuseStep 1671119 = 2506679) B2506679
theorem B2506703 : Blo 1670035 2506703 := bstep (se 1 (by rfl) ⟨1880027, by rfl⟩ : syracuseStep 2506703 = 3760055) B3760055
theorem B1671143 : Blo 1670035 1671143 := bstep (se 1 (by rfl) ⟨1253357, by rfl⟩ : syracuseStep 1671143 = 2506715) B2506715
theorem B8462555 : Blo 1670035 8462555 := bstep (se 1 (by rfl) ⟨6346916, by rfl⟩ : syracuseStep 8462555 = 12693833) B12693833
theorem B1671399 : Blo 1670035 1671399 := bstep (se 1 (by rfl) ⟨1253549, by rfl⟩ : syracuseStep 1671399 = 2507099) B2507099
theorem B3760415 : Blo 1670035 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B2507039 : Blo 1670035 2507039 := bstep (se 1 (by rfl) ⟨1880279, by rfl⟩ : syracuseStep 2507039 = 3760559) B3760559
theorem B2507063 : Blo 1670035 2507063 := bstep (se 1 (by rfl) ⟨1880297, by rfl⟩ : syracuseStep 2507063 = 3760595) B3760595
theorem B3170657 : Blo 1670035 3170657 := bstep (se 2 (by rfl) ⟨1188996, by rfl⟩ : syracuseStep 3170657 = 2377993) B2377993
theorem B8462717 : Blo 1670035 8462717 := bstep (se 3 (by rfl) ⟨1586759, by rfl⟩ : syracuseStep 8462717 = 3173519) B3173519
theorem B2507135 : Blo 1670035 2507135 := bstep (se 1 (by rfl) ⟨1880351, by rfl⟩ : syracuseStep 2507135 = 3760703) B3760703
theorem B1671551 : Blo 1670035 1671551 := bstep (se 1 (by rfl) ⟨1253663, by rfl⟩ : syracuseStep 1671551 = 2507327) B2507327
theorem B2507207 : Blo 1670035 2507207 := bstep (se 1 (by rfl) ⟨1880405, by rfl⟩ : syracuseStep 2507207 = 3760811) B3760811
theorem B1671631 : Blo 1670035 1671631 := bstep (se 1 (by rfl) ⟨1253723, by rfl⟩ : syracuseStep 1671631 = 2507447) B2507447
theorem B5636681 : Blo 1670035 5636681 := bstep (se 2 (by rfl) ⟨2113755, by rfl⟩ : syracuseStep 5636681 = 4227511) B4227511
theorem B1671783 : Blo 1670035 1671783 := bstep (se 1 (by rfl) ⟨1253837, by rfl⟩ : syracuseStep 1671783 = 2507675) B2507675
theorem B5636843 : Blo 1670035 5636843 := bstep (se 1 (by rfl) ⟨4227632, by rfl⟩ : syracuseStep 5636843 = 8455265) B8455265
theorem B27108107 : Blo 1670035 27108107 := bstep (se 1 (by rfl) ⟨20331080, by rfl⟩ : syracuseStep 27108107 = 40662161) B40662161
theorem B2507561 : Blo 1670035 2507561 := bstep (se 2 (by rfl) ⟨940335, by rfl⟩ : syracuseStep 2507561 = 1880671) B1880671
theorem B2507567 : Blo 1670035 2507567 := bstep (se 1 (by rfl) ⟨1880675, by rfl⟩ : syracuseStep 2507567 = 3761351) B3761351
theorem B2859887 : Blo 1670035 2859887 := bstep (se 1 (by rfl) ⟨2144915, by rfl⟩ : syracuseStep 2859887 = 4289831) B4289831
theorem B8815517 : Blo 1670035 8815517 := bstep (se 3 (by rfl) ⟨1652909, by rfl⟩ : syracuseStep 8815517 = 3305819) B3305819
theorem B3761063 : Blo 1670035 3761063 := bstep (se 1 (by rfl) ⟨2820797, by rfl⟩ : syracuseStep 3761063 = 5641595) B5641595
theorem B2507687 : Blo 1670035 2507687 := bstep (se 1 (by rfl) ⟨1880765, by rfl⟩ : syracuseStep 2507687 = 3761531) B3761531
theorem B12682169 : Blo 1670035 12682169 := bstep (se 2 (by rfl) ⟨4755813, by rfl⟩ : syracuseStep 12682169 = 9511627) B9511627
theorem B2507771 : Blo 1670035 2507771 := bstep (se 1 (by rfl) ⟨1880828, by rfl⟩ : syracuseStep 2507771 = 3761657) B3761657
theorem B2507831 : Blo 1670035 2507831 := bstep (se 1 (by rfl) ⟨1880873, by rfl⟩ : syracuseStep 2507831 = 3761747) B3761747
theorem B2507951 : Blo 1670035 2507951 := bstep (se 1 (by rfl) ⟨1880963, by rfl⟩ : syracuseStep 2507951 = 3761927) B3761927
theorem B2819279 : Blo 1670035 2819279 := bstep (se 1 (by rfl) ⟨2114459, by rfl⟩ : syracuseStep 2819279 = 4228919) B4228919
theorem B8455427 : Blo 1670035 8455427 := bstep (se 1 (by rfl) ⟨6341570, by rfl⟩ : syracuseStep 8455427 = 12683141) B12683141
theorem B12043691 : Blo 1670035 12043691 := bstep (se 1 (by rfl) ⟨9032768, by rfl⟩ : syracuseStep 12043691 = 18065537) B18065537
theorem B4515347 : Blo 1670035 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B16066097 : Blo 1670035 16066097 := bstep (se 2 (by rfl) ⟨6024786, by rfl⟩ : syracuseStep 16066097 = 12049573) B12049573
theorem B7136849 : Blo 1670035 7136849 := bstep (se 2 (by rfl) ⟨2676318, by rfl⟩ : syracuseStep 7136849 = 5352637) B5352637
theorem B6342239 : Blo 1670035 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B6022943 : Blo 1670035 6022943 := bstep (se 1 (by rfl) ⟨4517207, by rfl⟩ : syracuseStep 6022943 = 9034415) B9034415
theorem B2115391 : Blo 1670035 2115391 := bstep (se 1 (by rfl) ⟨1586543, by rfl⟩ : syracuseStep 2115391 = 3173087) B3173087
theorem B3761999 : Blo 1670035 3761999 := bstep (se 1 (by rfl) ⟨2821499, by rfl⟩ : syracuseStep 3761999 = 5642999) B5642999
theorem B3762017 : Blo 1670035 3762017 := bstep (se 2 (by rfl) ⟨1410756, by rfl⟩ : syracuseStep 3762017 = 2821513) B2821513
theorem B4229111 : Blo 1670035 4229111 := bstep (se 1 (by rfl) ⟨3171833, by rfl⟩ : syracuseStep 4229111 = 6343667) B6343667
theorem B2820089 : Blo 1670035 2820089 := bstep (se 2 (by rfl) ⟨1057533, by rfl⟩ : syracuseStep 2820089 = 2115067) B2115067
theorem B16058411 : Blo 1670035 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B9513085 : Blo 1670035 9513085 := bstep (se 3 (by rfl) ⟨1783703, by rfl⟩ : syracuseStep 9513085 = 3567407) B3567407
theorem B2820251 : Blo 1670035 2820251 := bstep (se 1 (by rfl) ⟨2115188, by rfl⟩ : syracuseStep 2820251 = 4230377) B4230377
theorem B5638355 : Blo 1670035 5638355 := bstep (se 1 (by rfl) ⟨4228766, by rfl⟩ : syracuseStep 5638355 = 8457533) B8457533
theorem B2820359 : Blo 1670035 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B5638625 : Blo 1670035 5638625 := bstep (se 2 (by rfl) ⟨2114484, by rfl⟩ : syracuseStep 5638625 = 4228969) B4228969
theorem B2820919 : Blo 1670035 2820919 := bstep (se 1 (by rfl) ⟨2115689, by rfl⟩ : syracuseStep 2820919 = 4231379) B4231379
theorem B8457047 : Blo 1670035 8457047 := bstep (se 1 (by rfl) ⟨6342785, by rfl⟩ : syracuseStep 8457047 = 12685571) B12685571
theorem B1878943 : Blo 1670035 1878943 := bstep (se 1 (by rfl) ⟨1409207, by rfl⟩ : syracuseStep 1878943 = 2818415) B2818415
theorem B57863099 : Blo 1670035 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B10701811 : Blo 1670035 10701811 := bstep (se 1 (by rfl) ⟨8026358, by rfl⟩ : syracuseStep 10701811 = 16052717) B16052717
theorem B195447809 : Blo 1670035 195447809 := bstep (se 2 (by rfl) ⟨73292928, by rfl⟩ : syracuseStep 195447809 = 146585857) B146585857
theorem B17386525 : Blo 1670035 17386525 := bstep (se 3 (by rfl) ⟨3259973, by rfl⟩ : syracuseStep 17386525 = 6519947) B6519947
theorem B1879087 : Blo 1670035 1879087 := bstep (se 1 (by rfl) ⟨1409315, by rfl⟩ : syracuseStep 1879087 = 2818631) B2818631
theorem B4230265 : Blo 1670035 4230265 := bstep (se 2 (by rfl) ⟨1586349, by rfl⟩ : syracuseStep 4230265 = 3172699) B3172699
theorem B6343879 : Blo 1670035 6343879 := bstep (se 1 (by rfl) ⟨4757909, by rfl⟩ : syracuseStep 6343879 = 9515819) B9515819
theorem B2821385 : Blo 1670035 2821385 := bstep (se 2 (by rfl) ⟨1058019, by rfl⟩ : syracuseStep 2821385 = 2116039) B2116039
theorem B1879375 : Blo 1670035 1879375 := bstep (se 1 (by rfl) ⟨1409531, by rfl⟩ : syracuseStep 1879375 = 2819063) B2819063
theorem B4230569 : Blo 1670035 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B26070673 : Blo 1670035 26070673 := bstep (se 2 (by rfl) ⟨9776502, by rfl⟩ : syracuseStep 26070673 = 19553005) B19553005
theorem B10702631 : Blo 1670035 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B5639975 : Blo 1670035 5639975 := bstep (se 1 (by rfl) ⟨4229981, by rfl⟩ : syracuseStep 5639975 = 8459963) B8459963
theorem B2379559 : Blo 1670035 2379559 := bstep (se 1 (by rfl) ⟨1784669, by rfl⟩ : syracuseStep 2379559 = 3569339) B3569339
theorem B1879879 : Blo 1670035 1879879 := bstep (se 1 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 1879879 = 2819819) B2819819
theorem B19296107 : Blo 1670035 19296107 := bstep (se 1 (by rfl) ⟨14472080, by rfl⟩ : syracuseStep 19296107 = 28944161) B28944161
theorem B3616633 : Blo 1670035 3616633 := bstep (se 2 (by rfl) ⟨1356237, by rfl⟩ : syracuseStep 3616633 = 2712475) B2712475
theorem B4231055 : Blo 1670035 4231055 := bstep (se 1 (by rfl) ⟨3173291, by rfl⟩ : syracuseStep 4231055 = 6346583) B6346583
theorem B144551951 : Blo 1670035 144551951 := bstep (se 1 (by rfl) ⟨108413963, by rfl⟩ : syracuseStep 144551951 = 216827927) B216827927
theorem B4886657 : Blo 1670035 4886657 := bstep (se 2 (by rfl) ⟨1832496, by rfl⟩ : syracuseStep 4886657 = 3664993) B3664993
theorem B21410183 : Blo 1670035 21410183 := bstep (se 1 (by rfl) ⟨16057637, by rfl⟩ : syracuseStep 21410183 = 32115275) B32115275
theorem B4231561 : Blo 1670035 4231561 := bstep (se 2 (by rfl) ⟨1586835, by rfl⟩ : syracuseStep 4231561 = 3173671) B3173671
theorem B1880527 : Blo 1670035 1880527 := bstep (se 1 (by rfl) ⟨1410395, by rfl⟩ : syracuseStep 1880527 = 2820791) B2820791
theorem B4231673 : Blo 1670035 4231673 := bstep (se 2 (by rfl) ⟨1586877, by rfl⟩ : syracuseStep 4231673 = 3173755) B3173755
theorem B19042937 : Blo 1670035 19042937 := bstep (se 2 (by rfl) ⟨7141101, by rfl⟩ : syracuseStep 19042937 = 14282203) B14282203
theorem B10703657 : Blo 1670035 10703657 := bstep (se 2 (by rfl) ⟨4013871, by rfl⟩ : syracuseStep 10703657 = 8027743) B8027743
theorem B5641001 : Blo 1670035 5641001 := bstep (se 2 (by rfl) ⟨2115375, by rfl⟩ : syracuseStep 5641001 = 4230751) B4230751
theorem B4756475 : Blo 1670035 4756475 := bstep (se 1 (by rfl) ⟨3567356, by rfl⟩ : syracuseStep 4756475 = 7134713) B7134713
theorem B5641271 : Blo 1670035 5641271 := bstep (se 1 (by rfl) ⟨4230953, by rfl⟩ : syracuseStep 5641271 = 8461907) B8461907
theorem B12039367 : Blo 1670035 12039367 := bstep (se 1 (by rfl) ⟨9029525, by rfl⟩ : syracuseStep 12039367 = 18059051) B18059051
theorem B9516275 : Blo 1670035 9516275 := bstep (se 1 (by rfl) ⟨7137206, by rfl⟩ : syracuseStep 9516275 = 14274413) B14274413
theorem B10712371 : Blo 1670035 10712371 := bstep (se 1 (by rfl) ⟨8034278, by rfl⟩ : syracuseStep 10712371 = 16068557) B16068557
theorem B8459639 : Blo 1670035 8459639 := bstep (se 1 (by rfl) ⟨6344729, by rfl⟩ : syracuseStep 8459639 = 12689459) B12689459
theorem B36140417 : Blo 1670035 36140417 := bstep (se 2 (by rfl) ⟨13552656, by rfl⟩ : syracuseStep 36140417 = 27105313) B27105313
theorem B51451361 : Blo 1670035 51451361 := bstep (se 2 (by rfl) ⟨19294260, by rfl⟩ : syracuseStep 51451361 = 38588521) B38588521
theorem B10589753 : Blo 1670035 10589753 := bstep (se 2 (by rfl) ⟨3971157, by rfl⟩ : syracuseStep 10589753 = 7942315) B7942315
theorem B12039769 : Blo 1670035 12039769 := bstep (se 2 (by rfl) ⟨4514913, by rfl⟩ : syracuseStep 12039769 = 9029827) B9029827
theorem B3757751 : Blo 1670035 3757751 := bstep (se 1 (by rfl) ⟨2818313, by rfl⟩ : syracuseStep 3757751 = 5636627) B5636627
theorem B5576663 : Blo 1670035 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B2144351 : Blo 1670035 2144351 := bstep (se 1 (by rfl) ⟨1608263, by rfl⟩ : syracuseStep 2144351 = 3216527) B3216527
theorem B4823183 : Blo 1670035 4823183 := bstep (se 1 (by rfl) ⟨3617387, by rfl⟩ : syracuseStep 4823183 = 7234775) B7234775
theorem B8460449 : Blo 1670035 8460449 := bstep (se 2 (by rfl) ⟨3172668, by rfl⟩ : syracuseStep 8460449 = 6345337) B6345337
theorem B8026283 : Blo 1670035 8026283 := bstep (se 1 (by rfl) ⟨6019712, by rfl⟩ : syracuseStep 8026283 = 12039425) B12039425
theorem B7141547 : Blo 1670035 7141547 := bstep (se 1 (by rfl) ⟨5356160, by rfl⟩ : syracuseStep 7141547 = 10712321) B10712321
theorem B5716267 : Blo 1670035 5716267 := bstep (se 1 (by rfl) ⟨4287200, by rfl⟩ : syracuseStep 5716267 = 8574401) B8574401
theorem B2505083 : Blo 1670035 2505083 := bstep (se 1 (by rfl) ⟨1878812, by rfl⟩ : syracuseStep 2505083 = 3757625) B3757625
theorem B2505353 : Blo 1670035 2505353 := bstep (se 2 (by rfl) ⟨939507, by rfl⟩ : syracuseStep 2505353 = 1879015) B1879015
theorem B4758173 : Blo 1670035 4758173 := bstep (se 3 (by rfl) ⟨892157, by rfl⟩ : syracuseStep 4758173 = 1784315) B1784315
theorem B2505527 : Blo 1670035 2505527 := bstep (se 1 (by rfl) ⟨1879145, by rfl⟩ : syracuseStep 2505527 = 3758291) B3758291
theorem B2505563 : Blo 1670035 2505563 := bstep (se 1 (by rfl) ⟨1879172, by rfl⟩ : syracuseStep 2505563 = 3758345) B3758345
theorem B3758939 : Blo 1670035 3758939 := bstep (se 1 (by rfl) ⟨2819204, by rfl⟩ : syracuseStep 3758939 = 5638409) B5638409
theorem B1670047 : Blo 1670035 1670047 := bstep (se 1 (by rfl) ⟨1252535, by rfl⟩ : syracuseStep 1670047 = 2505071) B2505071
theorem B2505707 : Blo 1670035 2505707 := bstep (se 1 (by rfl) ⟨1879280, by rfl⟩ : syracuseStep 2505707 = 3758561) B3758561
theorem B6347767 : Blo 1670035 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B1670191 : Blo 1670035 1670191 := bstep (se 1 (by rfl) ⟨1252643, by rfl⟩ : syracuseStep 1670191 = 2505287) B2505287
theorem B1670215 : Blo 1670035 1670215 := bstep (se 1 (by rfl) ⟨1252661, by rfl⟩ : syracuseStep 1670215 = 2505323) B2505323
theorem B8027207 : Blo 1670035 8027207 := bstep (se 1 (by rfl) ⟨6020405, by rfl⟩ : syracuseStep 8027207 = 12040811) B12040811
theorem B2505911 : Blo 1670035 2505911 := bstep (se 1 (by rfl) ⟨1879433, by rfl⟩ : syracuseStep 2505911 = 3758867) B3758867
theorem B42843329 : Blo 1670035 42843329 := bstep (se 2 (by rfl) ⟨16066248, by rfl⟩ : syracuseStep 42843329 = 32132497) B32132497
theorem B1670367 : Blo 1670035 1670367 := bstep (se 1 (by rfl) ⟨1252775, by rfl⟩ : syracuseStep 1670367 = 2505551) B2505551
theorem B21413159 : Blo 1670035 21413159 := bstep (se 1 (by rfl) ⟨16059869, by rfl⟩ : syracuseStep 21413159 = 32119739) B32119739
theorem B4013479 : Blo 1670035 4013479 := bstep (se 1 (by rfl) ⟨3010109, by rfl⟩ : syracuseStep 4013479 = 6020219) B6020219
theorem B2506151 : Blo 1670035 2506151 := bstep (se 1 (by rfl) ⟨1879613, by rfl⟩ : syracuseStep 2506151 = 3759227) B3759227
theorem B10853831 : Blo 1670035 10853831 := bstep (se 1 (by rfl) ⟨8140373, by rfl⟩ : syracuseStep 10853831 = 16280747) B16280747
theorem B1670631 : Blo 1670035 1670631 := bstep (se 1 (by rfl) ⟨1252973, by rfl⟩ : syracuseStep 1670631 = 2505947) B2505947
theorem B2506235 : Blo 1670035 2506235 := bstep (se 1 (by rfl) ⟨1879676, by rfl⟩ : syracuseStep 2506235 = 3759353) B3759353
theorem B2678267 : Blo 1670035 2678267 := bstep (se 1 (by rfl) ⟨2008700, by rfl⟩ : syracuseStep 2678267 = 4017401) B4017401
theorem B3759695 : Blo 1670035 3759695 := bstep (se 1 (by rfl) ⟨2819771, by rfl⟩ : syracuseStep 3759695 = 5639543) B5639543
theorem B2506331 : Blo 1670035 2506331 := bstep (se 1 (by rfl) ⟨1879748, by rfl⟩ : syracuseStep 2506331 = 3759497) B3759497
theorem B1670747 : Blo 1670035 1670747 := bstep (se 1 (by rfl) ⟨1253060, by rfl⟩ : syracuseStep 1670747 = 2506121) B2506121
theorem B9518735 : Blo 1670035 9518735 := bstep (se 1 (by rfl) ⟨7139051, by rfl⟩ : syracuseStep 9518735 = 14278103) B14278103
theorem B2506415 : Blo 1670035 2506415 := bstep (se 1 (by rfl) ⟨1879811, by rfl⟩ : syracuseStep 2506415 = 3759623) B3759623
theorem B2506535 : Blo 1670035 2506535 := bstep (se 1 (by rfl) ⟨1879901, by rfl⟩ : syracuseStep 2506535 = 3759803) B3759803
theorem B19029815 : Blo 1670035 19029815 := bstep (se 1 (by rfl) ⟨14272361, by rfl⟩ : syracuseStep 19029815 = 28544723) B28544723
theorem B1670983 : Blo 1670035 1670983 := bstep (se 1 (by rfl) ⟨1253237, by rfl⟩ : syracuseStep 1670983 = 2506475) B2506475
theorem B2506619 : Blo 1670035 2506619 := bstep (se 1 (by rfl) ⟨1879964, by rfl⟩ : syracuseStep 2506619 = 3759929) B3759929
theorem B14270417 : Blo 1670035 14270417 := bstep (se 2 (by rfl) ⟨5351406, by rfl⟩ : syracuseStep 14270417 = 10702813) B10702813
theorem B1671135 : Blo 1670035 1671135 := bstep (se 1 (by rfl) ⟨1253351, by rfl⟩ : syracuseStep 1671135 = 2506703) B2506703
theorem B2506943 : Blo 1670035 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B1671359 : Blo 1670035 1671359 := bstep (se 1 (by rfl) ⟨1253519, by rfl⟩ : syracuseStep 1671359 = 2507039) B2507039
theorem B1671375 : Blo 1670035 1671375 := bstep (se 1 (by rfl) ⟨1253531, by rfl⟩ : syracuseStep 1671375 = 2507063) B2507063
theorem B2113771 : Blo 1670035 2113771 := bstep (se 1 (by rfl) ⟨1585328, by rfl⟩ : syracuseStep 2113771 = 3170657) B3170657
theorem B5718269 : Blo 1670035 5718269 := bstep (se 3 (by rfl) ⟨1072175, by rfl⟩ : syracuseStep 5718269 = 2144351) B2144351
theorem B1671423 : Blo 1670035 1671423 := bstep (se 1 (by rfl) ⟨1253567, by rfl⟩ : syracuseStep 1671423 = 2507135) B2507135
theorem B1671471 : Blo 1670035 1671471 := bstep (se 1 (by rfl) ⟨1253603, by rfl⟩ : syracuseStep 1671471 = 2507207) B2507207
theorem B12861821 : Blo 1670035 12861821 := bstep (se 3 (by rfl) ⟨2411591, by rfl⟩ : syracuseStep 12861821 = 4823183) B4823183
theorem B18072071 : Blo 1670035 18072071 := bstep (se 1 (by rfl) ⟨13554053, by rfl⟩ : syracuseStep 18072071 = 27108107) B27108107
theorem B7135771 : Blo 1670035 7135771 := bstep (se 1 (by rfl) ⟨5351828, by rfl⟩ : syracuseStep 7135771 = 10703657) B10703657
theorem B3760667 : Blo 1670035 3760667 := bstep (se 1 (by rfl) ⟨2820500, by rfl⟩ : syracuseStep 3760667 = 5641001) B5641001
theorem B1671707 : Blo 1670035 1671707 := bstep (se 1 (by rfl) ⟨1253780, by rfl⟩ : syracuseStep 1671707 = 2507561) B2507561
theorem B1671711 : Blo 1670035 1671711 := bstep (se 1 (by rfl) ⟨1253783, by rfl⟩ : syracuseStep 1671711 = 2507567) B2507567
theorem B2507369 : Blo 1670035 2507369 := bstep (se 2 (by rfl) ⟨940263, by rfl⟩ : syracuseStep 2507369 = 1880527) B1880527
theorem B2507375 : Blo 1670035 2507375 := bstep (se 1 (by rfl) ⟨1880531, by rfl⟩ : syracuseStep 2507375 = 3761063) B3761063
theorem B1671791 : Blo 1670035 1671791 := bstep (se 1 (by rfl) ⟨1253843, by rfl⟩ : syracuseStep 1671791 = 2507687) B2507687
theorem B8454779 : Blo 1670035 8454779 := bstep (se 1 (by rfl) ⟨6341084, by rfl⟩ : syracuseStep 8454779 = 12682169) B12682169
theorem B3170983 : Blo 1670035 3170983 := bstep (se 1 (by rfl) ⟨2378237, by rfl⟩ : syracuseStep 3170983 = 4756475) B4756475
theorem B1671847 : Blo 1670035 1671847 := bstep (se 1 (by rfl) ⟨1253885, by rfl⟩ : syracuseStep 1671847 = 2507771) B2507771
theorem B3760847 : Blo 1670035 3760847 := bstep (se 1 (by rfl) ⟨2820635, by rfl⟩ : syracuseStep 3760847 = 5641271) B5641271
theorem B1671887 : Blo 1670035 1671887 := bstep (se 1 (by rfl) ⟨1253915, by rfl⟩ : syracuseStep 1671887 = 2507831) B2507831
theorem B1671967 : Blo 1670035 1671967 := bstep (se 1 (by rfl) ⟨1253975, by rfl⟩ : syracuseStep 1671967 = 2507951) B2507951
theorem B5636951 : Blo 1670035 5636951 := bstep (se 1 (by rfl) ⟨4227713, by rfl⟩ : syracuseStep 5636951 = 8455427) B8455427
theorem B121947029 : Blo 1670035 121947029 := bstep (se 6 (by rfl) ⟨2858133, by rfl⟩ : syracuseStep 121947029 = 5716267) B5716267
theorem B24093611 : Blo 1670035 24093611 := bstep (se 1 (by rfl) ⟨18070208, by rfl⟩ : syracuseStep 24093611 = 36140417) B36140417
theorem B8029127 : Blo 1670035 8029127 := bstep (se 1 (by rfl) ⟨6021845, by rfl⟩ : syracuseStep 8029127 = 12043691) B12043691
theorem B34300907 : Blo 1670035 34300907 := bstep (se 1 (by rfl) ⟨25725680, by rfl⟩ : syracuseStep 34300907 = 51451361) B51451361
theorem B4228159 : Blo 1670035 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B3761225 : Blo 1670035 3761225 := bstep (se 2 (by rfl) ⟨1410459, by rfl⟩ : syracuseStep 3761225 = 2820919) B2820919
theorem B4015295 : Blo 1670035 4015295 := bstep (se 1 (by rfl) ⟨3011471, by rfl⟩ : syracuseStep 4015295 = 6022943) B6022943
theorem B2507999 : Blo 1670035 2507999 := bstep (se 1 (by rfl) ⟨1880999, by rfl⟩ : syracuseStep 2507999 = 3761999) B3761999
theorem B2508011 : Blo 1670035 2508011 := bstep (se 1 (by rfl) ⟨1881008, by rfl⟩ : syracuseStep 2508011 = 3762017) B3762017
theorem B8463689 : Blo 1670035 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B2819407 : Blo 1670035 2819407 := bstep (se 1 (by rfl) ⟨2114555, by rfl⟩ : syracuseStep 2819407 = 4229111) B4229111
theorem B5350855 : Blo 1670035 5350855 := bstep (se 1 (by rfl) ⟨4013141, by rfl⟩ : syracuseStep 5350855 = 8026283) B8026283
theorem B4761031 : Blo 1670035 4761031 := bstep (se 1 (by rfl) ⟨3570773, by rfl⟩ : syracuseStep 4761031 = 7141547) B7141547
theorem B3172115 : Blo 1670035 3172115 := bstep (se 1 (by rfl) ⟨2379086, by rfl⟩ : syracuseStep 3172115 = 4758173) B4758173
theorem B5351305 : Blo 1670035 5351305 := bstep (se 2 (by rfl) ⟨2006739, by rfl⟩ : syracuseStep 5351305 = 4013479) B4013479
theorem B5638031 : Blo 1670035 5638031 := bstep (se 1 (by rfl) ⟨4228523, by rfl⟩ : syracuseStep 5638031 = 8457047) B8457047
theorem B5351471 : Blo 1670035 5351471 := bstep (se 1 (by rfl) ⟨4013603, by rfl⟩ : syracuseStep 5351471 = 8027207) B8027207
theorem B34760897 : Blo 1670035 34760897 := bstep (se 2 (by rfl) ⟨13035336, by rfl⟩ : syracuseStep 34760897 = 26070673) B26070673
theorem B2820379 : Blo 1670035 2820379 := bstep (se 1 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 2820379 = 4230569) B4230569
theorem B7235887 : Blo 1670035 7235887 := bstep (se 1 (by rfl) ⟨5426915, by rfl⟩ : syracuseStep 7235887 = 10853831) B10853831
theorem B3172745 : Blo 1670035 3172745 := bstep (se 2 (by rfl) ⟨1189779, by rfl⟩ : syracuseStep 3172745 = 2379559) B2379559
theorem B2820521 : Blo 1670035 2820521 := bstep (se 2 (by rfl) ⟨1057695, by rfl⟩ : syracuseStep 2820521 = 2115391) B2115391
theorem B12864071 : Blo 1670035 12864071 := bstep (se 1 (by rfl) ⟨9648053, by rfl⟩ : syracuseStep 12864071 = 19296107) B19296107
theorem B2820703 : Blo 1670035 2820703 := bstep (se 1 (by rfl) ⟨2115527, by rfl⟩ : syracuseStep 2820703 = 4231055) B4231055
theorem B9513611 : Blo 1670035 9513611 := bstep (se 1 (by rfl) ⟨7135208, by rfl⟩ : syracuseStep 9513611 = 14270417) B14270417
theorem B12684113 : Blo 1670035 12684113 := bstep (se 2 (by rfl) ⟨4756542, by rfl⟩ : syracuseStep 12684113 = 9513085) B9513085
theorem B14273455 : Blo 1670035 14273455 := bstep (se 1 (by rfl) ⟨10705091, by rfl⟩ : syracuseStep 14273455 = 21410183) B21410183
theorem B2821115 : Blo 1670035 2821115 := bstep (se 1 (by rfl) ⟨2115836, by rfl⟩ : syracuseStep 2821115 = 4231673) B4231673
theorem B5877011 : Blo 1670035 5877011 := bstep (se 1 (by rfl) ⟨4407758, by rfl⟩ : syracuseStep 5877011 = 8815517) B8815517
theorem B1879519 : Blo 1670035 1879519 := bstep (se 1 (by rfl) ⟨1409639, by rfl⟩ : syracuseStep 1879519 = 2819279) B2819279
theorem B6344183 : Blo 1670035 6344183 := bstep (se 1 (by rfl) ⟨4758137, by rfl⟩ : syracuseStep 6344183 = 9516275) B9516275
theorem B5639759 : Blo 1670035 5639759 := bstep (se 1 (by rfl) ⟨4229819, by rfl⟩ : syracuseStep 5639759 = 8459639) B8459639
theorem B3010231 : Blo 1670035 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B10710731 : Blo 1670035 10710731 := bstep (se 1 (by rfl) ⟨8033048, by rfl⟩ : syracuseStep 10710731 = 16066097) B16066097
theorem B1880059 : Blo 1670035 1880059 := bstep (se 1 (by rfl) ⟨1410044, by rfl⟩ : syracuseStep 1880059 = 2820089) B2820089
theorem B1880167 : Blo 1670035 1880167 := bstep (se 1 (by rfl) ⟨1410125, by rfl⟩ : syracuseStep 1880167 = 2820251) B2820251
theorem B5640299 : Blo 1670035 5640299 := bstep (se 1 (by rfl) ⟨4230224, by rfl⟩ : syracuseStep 5640299 = 8460449) B8460449
theorem B5640353 : Blo 1670035 5640353 := bstep (se 2 (by rfl) ⟨2115132, by rfl⟩ : syracuseStep 5640353 = 4230265) B4230265
theorem B1880239 : Blo 1670035 1880239 := bstep (se 1 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 1880239 = 2820359) B2820359
theorem B16052489 : Blo 1670035 16052489 := bstep (se 2 (by rfl) ⟨6019683, by rfl⟩ : syracuseStep 16052489 = 12039367) B12039367
theorem B8458505 : Blo 1670035 8458505 := bstep (se 2 (by rfl) ⟨3171939, by rfl⟩ : syracuseStep 8458505 = 6343879) B6343879
theorem B14283161 : Blo 1670035 14283161 := bstep (se 2 (by rfl) ⟨5356185, by rfl⟩ : syracuseStep 14283161 = 10712371) B10712371
theorem B19288709 : Blo 1670035 19288709 := bstep (se 4 (by rfl) ⟨1808316, by rfl⟩ : syracuseStep 19288709 = 3616633) B3616633
theorem B130298539 : Blo 1670035 130298539 := bstep (se 1 (by rfl) ⟨97723904, by rfl⟩ : syracuseStep 130298539 = 195447809) B195447809
theorem B16053025 : Blo 1670035 16053025 := bstep (se 2 (by rfl) ⟨6019884, by rfl⟩ : syracuseStep 16053025 = 12039769) B12039769
theorem B28562219 : Blo 1670035 28562219 := bstep (se 1 (by rfl) ⟨21421664, by rfl⟩ : syracuseStep 28562219 = 42843329) B42843329
theorem B1880923 : Blo 1670035 1880923 := bstep (se 1 (by rfl) ⟨1410692, by rfl⟩ : syracuseStep 1880923 = 2821385) B2821385
theorem B14275439 : Blo 1670035 14275439 := bstep (se 1 (by rfl) ⟨10706579, by rfl⟩ : syracuseStep 14275439 = 21413159) B21413159
theorem B6345823 : Blo 1670035 6345823 := bstep (se 1 (by rfl) ⟨4759367, by rfl⟩ : syracuseStep 6345823 = 9518735) B9518735
theorem B12686543 : Blo 1670035 12686543 := bstep (se 1 (by rfl) ⟨9514907, by rfl⟩ : syracuseStep 12686543 = 19029815) B19029815
theorem B96367967 : Blo 1670035 96367967 := bstep (se 1 (by rfl) ⟨72275975, by rfl⟩ : syracuseStep 96367967 = 144551951) B144551951
theorem B3257771 : Blo 1670035 3257771 := bstep (se 1 (by rfl) ⟨2443328, by rfl⟩ : syracuseStep 3257771 = 4886657) B4886657
theorem B5641703 : Blo 1670035 5641703 := bstep (se 1 (by rfl) ⟨4231277, by rfl⟩ : syracuseStep 5641703 = 8462555) B8462555
theorem B5641811 : Blo 1670035 5641811 := bstep (se 1 (by rfl) ⟨4231358, by rfl⟩ : syracuseStep 5641811 = 8462717) B8462717
theorem B3757787 : Blo 1670035 3757787 := bstep (se 1 (by rfl) ⟨2818340, by rfl⟩ : syracuseStep 3757787 = 5636681) B5636681
theorem B12695291 : Blo 1670035 12695291 := bstep (se 1 (by rfl) ⟨9521468, by rfl⟩ : syracuseStep 12695291 = 19042937) B19042937
theorem B3757895 : Blo 1670035 3757895 := bstep (se 1 (by rfl) ⟨2818421, by rfl⟩ : syracuseStep 3757895 = 5636843) B5636843
theorem B5642081 : Blo 1670035 5642081 := bstep (se 2 (by rfl) ⟨2115780, by rfl⟩ : syracuseStep 5642081 = 4231561) B4231561
theorem B1906591 : Blo 1670035 1906591 := bstep (se 1 (by rfl) ⟨1429943, by rfl⟩ : syracuseStep 1906591 = 2859887) B2859887
theorem B7059835 : Blo 1670035 7059835 := bstep (se 1 (by rfl) ⟨5294876, by rfl⟩ : syracuseStep 7059835 = 10589753) B10589753
theorem B4757899 : Blo 1670035 4757899 := bstep (se 1 (by rfl) ⟨3568424, by rfl⟩ : syracuseStep 4757899 = 7136849) B7136849
theorem B2505167 : Blo 1670035 2505167 := bstep (se 1 (by rfl) ⟨1878875, by rfl⟩ : syracuseStep 2505167 = 3757751) B3757751
theorem B2505257 : Blo 1670035 2505257 := bstep (se 2 (by rfl) ⟨939471, by rfl⟩ : syracuseStep 2505257 = 1878943) B1878943
theorem B3717775 : Blo 1670035 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B14269081 : Blo 1670035 14269081 := bstep (se 2 (by rfl) ⟨5350905, by rfl⟩ : syracuseStep 14269081 = 10701811) B10701811
theorem B10705607 : Blo 1670035 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B23182033 : Blo 1670035 23182033 := bstep (se 2 (by rfl) ⟨8693262, by rfl⟩ : syracuseStep 23182033 = 17386525) B17386525
theorem B2505449 : Blo 1670035 2505449 := bstep (se 2 (by rfl) ⟨939543, by rfl⟩ : syracuseStep 2505449 = 1879087) B1879087
theorem B3758903 : Blo 1670035 3758903 := bstep (se 1 (by rfl) ⟨2819177, by rfl⟩ : syracuseStep 3758903 = 5638355) B5638355
theorem B1670055 : Blo 1670035 1670055 := bstep (se 1 (by rfl) ⟨1252541, by rfl⟩ : syracuseStep 1670055 = 2505083) B2505083
theorem B3759083 : Blo 1670035 3759083 := bstep (se 1 (by rfl) ⟨2819312, by rfl⟩ : syracuseStep 3759083 = 5638625) B5638625
theorem B1670235 : Blo 1670035 1670235 := bstep (se 1 (by rfl) ⟨1252676, by rfl⟩ : syracuseStep 1670235 = 2505353) B2505353
theorem B2505833 : Blo 1670035 2505833 := bstep (se 2 (by rfl) ⟨939687, by rfl⟩ : syracuseStep 2505833 = 1879375) B1879375
theorem B1670351 : Blo 1670035 1670351 := bstep (se 1 (by rfl) ⟨1252763, by rfl⟩ : syracuseStep 1670351 = 2505527) B2505527
theorem B1670375 : Blo 1670035 1670375 := bstep (se 1 (by rfl) ⟨1252781, by rfl⟩ : syracuseStep 1670375 = 2505563) B2505563
theorem B2505959 : Blo 1670035 2505959 := bstep (se 1 (by rfl) ⟨1879469, by rfl⟩ : syracuseStep 2505959 = 3758939) B3758939
theorem B38575399 : Blo 1670035 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B1670471 : Blo 1670035 1670471 := bstep (se 1 (by rfl) ⟨1252853, by rfl⟩ : syracuseStep 1670471 = 2505707) B2505707
theorem B28540349 : Blo 1670035 28540349 := bstep (se 3 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 28540349 = 10702631) B10702631
theorem B1670607 : Blo 1670035 1670607 := bstep (se 1 (by rfl) ⟨1252955, by rfl⟩ : syracuseStep 1670607 = 2505911) B2505911
theorem B1670767 : Blo 1670035 1670767 := bstep (se 1 (by rfl) ⟨1253075, by rfl⟩ : syracuseStep 1670767 = 2506151) B2506151
theorem B1670823 : Blo 1670035 1670823 := bstep (se 1 (by rfl) ⟨1253117, by rfl⟩ : syracuseStep 1670823 = 2506235) B2506235
theorem B1785511 : Blo 1670035 1785511 := bstep (se 1 (by rfl) ⟨1339133, by rfl⟩ : syracuseStep 1785511 = 2678267) B2678267
theorem B2506463 : Blo 1670035 2506463 := bstep (se 1 (by rfl) ⟨1879847, by rfl⟩ : syracuseStep 2506463 = 3759695) B3759695
theorem B1670887 : Blo 1670035 1670887 := bstep (se 1 (by rfl) ⟨1253165, by rfl⟩ : syracuseStep 1670887 = 2506331) B2506331
theorem B2506505 : Blo 1670035 2506505 := bstep (se 2 (by rfl) ⟨939939, by rfl⟩ : syracuseStep 2506505 = 1879879) B1879879
theorem B1670943 : Blo 1670035 1670943 := bstep (se 1 (by rfl) ⟨1253207, by rfl⟩ : syracuseStep 1670943 = 2506415) B2506415
theorem B1671023 : Blo 1670035 1671023 := bstep (se 1 (by rfl) ⟨1253267, by rfl⟩ : syracuseStep 1671023 = 2506535) B2506535
theorem B3759983 : Blo 1670035 3759983 := bstep (se 1 (by rfl) ⟨2819987, by rfl⟩ : syracuseStep 3759983 = 5639975) B5639975
theorem B1671079 : Blo 1670035 1671079 := bstep (se 1 (by rfl) ⟨1253309, by rfl⟩ : syracuseStep 1671079 = 2506619) B2506619
theorem B3760199 : Blo 1670035 3760199 := bstep (se 1 (by rfl) ⟨2820149, by rfl⟩ : syracuseStep 3760199 = 5640299) B5640299
theorem B3760235 : Blo 1670035 3760235 := bstep (se 1 (by rfl) ⟨2820176, by rfl⟩ : syracuseStep 3760235 = 5640353) B5640353
theorem B1671295 : Blo 1670035 1671295 := bstep (se 1 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 1671295 = 2506943) B2506943
theorem B2506889 : Blo 1670035 2506889 := bstep (se 2 (by rfl) ⟨940083, by rfl⟩ : syracuseStep 2506889 = 1880167) B1880167
theorem B2506985 : Blo 1670035 2506985 := bstep (se 2 (by rfl) ⟨940119, by rfl⟩ : syracuseStep 2506985 = 1880239) B1880239
theorem B2818361 : Blo 1670035 2818361 := bstep (se 2 (by rfl) ⟨1056885, by rfl⟩ : syracuseStep 2818361 = 2113771) B2113771
theorem B2507111 : Blo 1670035 2507111 := bstep (se 1 (by rfl) ⟨1880333, by rfl⟩ : syracuseStep 2507111 = 3760667) B3760667
theorem B3760505 : Blo 1670035 3760505 := bstep (se 2 (by rfl) ⟨1410189, by rfl⟩ : syracuseStep 3760505 = 2820379) B2820379
theorem B1671579 : Blo 1670035 1671579 := bstep (se 1 (by rfl) ⟨1253684, by rfl⟩ : syracuseStep 1671579 = 2507369) B2507369
theorem B1671583 : Blo 1670035 1671583 := bstep (se 1 (by rfl) ⟨1253687, by rfl⟩ : syracuseStep 1671583 = 2507375) B2507375
theorem B5636519 : Blo 1670035 5636519 := bstep (se 1 (by rfl) ⟨4227389, by rfl⟩ : syracuseStep 5636519 = 8454779) B8454779
theorem B2507231 : Blo 1670035 2507231 := bstep (se 1 (by rfl) ⟨1880423, by rfl⟩ : syracuseStep 2507231 = 3760847) B3760847
theorem B81298019 : Blo 1670035 81298019 := bstep (se 1 (by rfl) ⟨60973514, by rfl⟩ : syracuseStep 81298019 = 121947029) B121947029
theorem B2507483 : Blo 1670035 2507483 := bstep (se 1 (by rfl) ⟨1880612, by rfl⟩ : syracuseStep 2507483 = 3761225) B3761225
theorem B3760937 : Blo 1670035 3760937 := bstep (se 2 (by rfl) ⟨1410351, by rfl⟩ : syracuseStep 3760937 = 2820703) B2820703
theorem B1671999 : Blo 1670035 1671999 := bstep (se 1 (by rfl) ⟨1253999, by rfl⟩ : syracuseStep 1671999 = 2507999) B2507999
theorem B1672007 : Blo 1670035 1672007 := bstep (se 1 (by rfl) ⟨1254005, by rfl⟩ : syracuseStep 1672007 = 2508011) B2508011
theorem B4957033 : Blo 1670035 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B4227977 : Blo 1670035 4227977 := bstep (se 2 (by rfl) ⟨1585491, by rfl⟩ : syracuseStep 4227977 = 3170983) B3170983
theorem B30909377 : Blo 1670035 30909377 := bstep (se 2 (by rfl) ⟨11591016, by rfl⟩ : syracuseStep 30909377 = 23182033) B23182033
theorem B3761135 : Blo 1670035 3761135 := bstep (se 1 (by rfl) ⟨2820851, by rfl⟩ : syracuseStep 3761135 = 5641703) B5641703
theorem B3761207 : Blo 1670035 3761207 := bstep (se 1 (by rfl) ⟨2820905, by rfl⟩ : syracuseStep 3761207 = 5641811) B5641811
theorem B2507897 : Blo 1670035 2507897 := bstep (se 2 (by rfl) ⟨940461, by rfl⟩ : syracuseStep 2507897 = 1880923) B1880923
theorem B8463527 : Blo 1670035 8463527 := bstep (se 1 (by rfl) ⟨6347645, by rfl⟩ : syracuseStep 8463527 = 12695291) B12695291
theorem B2114743 : Blo 1670035 2114743 := bstep (se 1 (by rfl) ⟨1586057, by rfl⟩ : syracuseStep 2114743 = 3172115) B3172115
theorem B19031273 : Blo 1670035 19031273 := bstep (se 2 (by rfl) ⟨7136727, by rfl⟩ : syracuseStep 19031273 = 14273455) B14273455
theorem B3761387 : Blo 1670035 3761387 := bstep (se 1 (by rfl) ⟨2821040, by rfl⟩ : syracuseStep 3761387 = 5642081) B5642081
theorem B5637545 : Blo 1670035 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B2115163 : Blo 1670035 2115163 := bstep (se 1 (by rfl) ⟨1586372, by rfl⟩ : syracuseStep 2115163 = 3172745) B3172745
theorem B6342407 : Blo 1670035 6342407 := bstep (se 1 (by rfl) ⟨4756805, by rfl⟩ : syracuseStep 6342407 = 9513611) B9513611
theorem B7137071 : Blo 1670035 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B8456075 : Blo 1670035 8456075 := bstep (se 1 (by rfl) ⟨6342056, by rfl⟩ : syracuseStep 8456075 = 12684113) B12684113
theorem B37652453 : Blo 1670035 37652453 := bstep (se 4 (by rfl) ⟨3529917, by rfl⟩ : syracuseStep 37652453 = 7059835) B7059835
theorem B3918007 : Blo 1670035 3918007 := bstep (se 1 (by rfl) ⟨2938505, by rfl⟩ : syracuseStep 3918007 = 5877011) B5877011
theorem B4229455 : Blo 1670035 4229455 := bstep (se 1 (by rfl) ⟨3172091, by rfl⟩ : syracuseStep 4229455 = 6344183) B6344183
theorem B2542121 : Blo 1670035 2542121 := bstep (se 2 (by rfl) ⟨953295, by rfl⟩ : syracuseStep 2542121 = 1906591) B1906591
theorem B3812179 : Blo 1670035 3812179 := bstep (se 1 (by rfl) ⟨2859134, by rfl⟩ : syracuseStep 3812179 = 5718269) B5718269
theorem B10701659 : Blo 1670035 10701659 := bstep (se 1 (by rfl) ⟨8026244, by rfl⟩ : syracuseStep 10701659 = 16052489) B16052489
theorem B5639003 : Blo 1670035 5639003 := bstep (se 1 (by rfl) ⟨4229252, by rfl⟩ : syracuseStep 5639003 = 8458505) B8458505
theorem B9522107 : Blo 1670035 9522107 := bstep (se 1 (by rfl) ⟨7141580, by rfl⟩ : syracuseStep 9522107 = 14283161) B14283161
theorem B6343865 : Blo 1670035 6343865 := bstep (se 2 (by rfl) ⟨2378949, by rfl⟩ : syracuseStep 6343865 = 4757899) B4757899
theorem B19041479 : Blo 1670035 19041479 := bstep (se 1 (by rfl) ⟨14281109, by rfl⟩ : syracuseStep 19041479 = 28562219) B28562219
theorem B5352751 : Blo 1670035 5352751 := bstep (se 1 (by rfl) ⟨4014563, by rfl⟩ : syracuseStep 5352751 = 8029127) B8029127
theorem B22867271 : Blo 1670035 22867271 := bstep (se 1 (by rfl) ⟨17150453, by rfl⟩ : syracuseStep 22867271 = 34300907) B34300907
theorem B9514361 : Blo 1670035 9514361 := bstep (se 2 (by rfl) ⟨3567885, by rfl⟩ : syracuseStep 9514361 = 7135771) B7135771
theorem B8457695 : Blo 1670035 8457695 := bstep (se 1 (by rfl) ⟨6343271, by rfl⟩ : syracuseStep 8457695 = 12686543) B12686543
theorem B19025441 : Blo 1670035 19025441 := bstep (se 2 (by rfl) ⟨7134540, by rfl⟩ : syracuseStep 19025441 = 14269081) B14269081
theorem B173731385 : Blo 1670035 173731385 := bstep (se 2 (by rfl) ⟨65149269, by rfl⟩ : syracuseStep 173731385 = 130298539) B130298539
theorem B64245311 : Blo 1670035 64245311 := bstep (se 1 (by rfl) ⟨48183983, by rfl⟩ : syracuseStep 64245311 = 96367967) B96367967
theorem B8687389 : Blo 1670035 8687389 := bstep (se 3 (by rfl) ⟨1628885, by rfl⟩ : syracuseStep 8687389 = 3257771) B3257771
theorem B3567647 : Blo 1670035 3567647 := bstep (se 1 (by rfl) ⟨2675735, by rfl⟩ : syracuseStep 3567647 = 5351471) B5351471
theorem B1880347 : Blo 1670035 1880347 := bstep (se 1 (by rfl) ⟨1410260, by rfl⟩ : syracuseStep 1880347 = 2820521) B2820521
theorem B51433865 : Blo 1670035 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B1880743 : Blo 1670035 1880743 := bstep (se 1 (by rfl) ⟨1410557, by rfl⟩ : syracuseStep 1880743 = 2821115) B2821115
theorem B2380681 : Blo 1670035 2380681 := bstep (se 2 (by rfl) ⟨892755, by rfl⟩ : syracuseStep 2380681 = 1785511) B1785511
theorem B19026899 : Blo 1670035 19026899 := bstep (se 1 (by rfl) ⟨14270174, by rfl⟩ : syracuseStep 19026899 = 28540349) B28540349
theorem B7140487 : Blo 1670035 7140487 := bstep (se 1 (by rfl) ⟨5355365, by rfl⟩ : syracuseStep 7140487 = 10710731) B10710731
theorem B8574547 : Blo 1670035 8574547 := bstep (se 1 (by rfl) ⟨6430910, by rfl⟩ : syracuseStep 8574547 = 12861821) B12861821
theorem B12048047 : Blo 1670035 12048047 := bstep (se 1 (by rfl) ⟨9036035, by rfl⟩ : syracuseStep 12048047 = 18072071) B18072071
theorem B9647849 : Blo 1670035 9647849 := bstep (se 2 (by rfl) ⟨3617943, by rfl⟩ : syracuseStep 9647849 = 7235887) B7235887
theorem B12859139 : Blo 1670035 12859139 := bstep (se 1 (by rfl) ⟨9644354, by rfl⟩ : syracuseStep 12859139 = 19288709) B19288709
theorem B3757967 : Blo 1670035 3757967 := bstep (se 1 (by rfl) ⟨2818475, by rfl⟩ : syracuseStep 3757967 = 5636951) B5636951
theorem B9516959 : Blo 1670035 9516959 := bstep (se 1 (by rfl) ⟨7137719, by rfl⟩ : syracuseStep 9516959 = 14275439) B14275439
theorem B16062407 : Blo 1670035 16062407 := bstep (se 1 (by rfl) ⟨12046805, by rfl⟩ : syracuseStep 16062407 = 24093611) B24093611
theorem B2676863 : Blo 1670035 2676863 := bstep (se 1 (by rfl) ⟨2007647, by rfl⟩ : syracuseStep 2676863 = 4015295) B4015295
theorem B5642459 : Blo 1670035 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B21404033 : Blo 1670035 21404033 := bstep (se 2 (by rfl) ⟨8026512, by rfl⟩ : syracuseStep 21404033 = 16053025) B16053025
theorem B2505191 : Blo 1670035 2505191 := bstep (se 1 (by rfl) ⟨1878893, by rfl⟩ : syracuseStep 2505191 = 3757787) B3757787
theorem B2505263 : Blo 1670035 2505263 := bstep (se 1 (by rfl) ⟨1878947, by rfl⟩ : syracuseStep 2505263 = 3757895) B3757895
theorem B3758687 : Blo 1670035 3758687 := bstep (se 1 (by rfl) ⟨2819015, by rfl⟩ : syracuseStep 3758687 = 5638031) B5638031
theorem B8461097 : Blo 1670035 8461097 := bstep (se 2 (by rfl) ⟨3172911, by rfl⟩ : syracuseStep 8461097 = 6345823) B6345823
theorem B23173931 : Blo 1670035 23173931 := bstep (se 1 (by rfl) ⟨17380448, by rfl⟩ : syracuseStep 23173931 = 34760897) B34760897
theorem B1670111 : Blo 1670035 1670111 := bstep (se 1 (by rfl) ⟨1252583, by rfl⟩ : syracuseStep 1670111 = 2505167) B2505167
theorem B1670171 : Blo 1670035 1670171 := bstep (se 1 (by rfl) ⟨1252628, by rfl⟩ : syracuseStep 1670171 = 2505257) B2505257
theorem B8576047 : Blo 1670035 8576047 := bstep (se 1 (by rfl) ⟨6432035, by rfl⟩ : syracuseStep 8576047 = 12864071) B12864071
theorem B3759209 : Blo 1670035 3759209 := bstep (se 2 (by rfl) ⟨1409703, by rfl⟩ : syracuseStep 3759209 = 2819407) B2819407
theorem B1670299 : Blo 1670035 1670299 := bstep (se 1 (by rfl) ⟨1252724, by rfl⟩ : syracuseStep 1670299 = 2505449) B2505449
theorem B2505935 : Blo 1670035 2505935 := bstep (se 1 (by rfl) ⟨1879451, by rfl⟩ : syracuseStep 2505935 = 3758903) B3758903
theorem B7134473 : Blo 1670035 7134473 := bstep (se 2 (by rfl) ⟨2675427, by rfl⟩ : syracuseStep 7134473 = 5350855) B5350855
theorem B6348041 : Blo 1670035 6348041 := bstep (se 2 (by rfl) ⟨2380515, by rfl⟩ : syracuseStep 6348041 = 4761031) B4761031
theorem B2506025 : Blo 1670035 2506025 := bstep (se 2 (by rfl) ⟨939759, by rfl⟩ : syracuseStep 2506025 = 1879519) B1879519
theorem B2506055 : Blo 1670035 2506055 := bstep (se 1 (by rfl) ⟨1879541, by rfl⟩ : syracuseStep 2506055 = 3759083) B3759083
theorem B1670555 : Blo 1670035 1670555 := bstep (se 1 (by rfl) ⟨1252916, by rfl⟩ : syracuseStep 1670555 = 2505833) B2505833
theorem B1670639 : Blo 1670035 1670639 := bstep (se 1 (by rfl) ⟨1252979, by rfl⟩ : syracuseStep 1670639 = 2505959) B2505959
theorem B4013641 : Blo 1670035 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B3759839 : Blo 1670035 3759839 := bstep (se 1 (by rfl) ⟨2819879, by rfl⟩ : syracuseStep 3759839 = 5639759) B5639759
theorem B1670975 : Blo 1670035 1670975 := bstep (se 1 (by rfl) ⟨1253231, by rfl⟩ : syracuseStep 1670975 = 2506463) B2506463
theorem B1671003 : Blo 1670035 1671003 := bstep (se 1 (by rfl) ⟨1253252, by rfl⟩ : syracuseStep 1671003 = 2506505) B2506505
theorem B7135073 : Blo 1670035 7135073 := bstep (se 2 (by rfl) ⟨2675652, by rfl⟩ : syracuseStep 7135073 = 5351305) B5351305
theorem B2506655 : Blo 1670035 2506655 := bstep (se 1 (by rfl) ⟨1879991, by rfl⟩ : syracuseStep 2506655 = 3759983) B3759983
theorem B2506745 : Blo 1670035 2506745 := bstep (se 2 (by rfl) ⟨940029, by rfl⟩ : syracuseStep 2506745 = 1880059) B1880059
theorem B2506799 : Blo 1670035 2506799 := bstep (se 1 (by rfl) ⟨1880099, by rfl⟩ : syracuseStep 2506799 = 3760199) B3760199
theorem B2506823 : Blo 1670035 2506823 := bstep (se 1 (by rfl) ⟨1880117, by rfl⟩ : syracuseStep 2506823 = 3760235) B3760235
theorem B1671259 : Blo 1670035 1671259 := bstep (se 1 (by rfl) ⟨1253444, by rfl⟩ : syracuseStep 1671259 = 2506889) B2506889
theorem B1671323 : Blo 1670035 1671323 := bstep (se 1 (by rfl) ⟨1253492, by rfl⟩ : syracuseStep 1671323 = 2506985) B2506985
theorem B1671407 : Blo 1670035 1671407 := bstep (se 1 (by rfl) ⟨1253555, by rfl⟩ : syracuseStep 1671407 = 2507111) B2507111
theorem B2507003 : Blo 1670035 2507003 := bstep (se 1 (by rfl) ⟨1880252, by rfl⟩ : syracuseStep 2507003 = 3760505) B3760505
theorem B1671487 : Blo 1670035 1671487 := bstep (se 1 (by rfl) ⟨1253615, by rfl⟩ : syracuseStep 1671487 = 2507231) B2507231
theorem B2507129 : Blo 1670035 2507129 := bstep (se 2 (by rfl) ⟨940173, by rfl⟩ : syracuseStep 2507129 = 1880347) B1880347
theorem B54198679 : Blo 1670035 54198679 := bstep (se 1 (by rfl) ⟨40649009, by rfl⟩ : syracuseStep 54198679 = 81298019) B81298019
theorem B1671655 : Blo 1670035 1671655 := bstep (se 1 (by rfl) ⟨1253741, by rfl⟩ : syracuseStep 1671655 = 2507483) B2507483
theorem B2507291 : Blo 1670035 2507291 := bstep (se 1 (by rfl) ⟨1880468, by rfl⟩ : syracuseStep 2507291 = 3760937) B3760937
theorem B2818651 : Blo 1670035 2818651 := bstep (se 1 (by rfl) ⟨2113988, by rfl⟩ : syracuseStep 2818651 = 4227977) B4227977
theorem B2507423 : Blo 1670035 2507423 := bstep (se 1 (by rfl) ⟨1880567, by rfl⟩ : syracuseStep 2507423 = 3761135) B3761135
theorem B2507471 : Blo 1670035 2507471 := bstep (se 1 (by rfl) ⟨1880603, by rfl⟩ : syracuseStep 2507471 = 3761207) B3761207
theorem B1671931 : Blo 1670035 1671931 := bstep (se 1 (by rfl) ⟨1253948, by rfl⟩ : syracuseStep 1671931 = 2507897) B2507897
theorem B2507591 : Blo 1670035 2507591 := bstep (se 1 (by rfl) ⟨1880693, by rfl⟩ : syracuseStep 2507591 = 3761387) B3761387
theorem B2507657 : Blo 1670035 2507657 := bstep (se 2 (by rfl) ⟨940371, by rfl⟩ : syracuseStep 2507657 = 1880743) B1880743
theorem B6431899 : Blo 1670035 6431899 := bstep (se 1 (by rfl) ⟨4823924, by rfl⟩ : syracuseStep 6431899 = 9647849) B9647849
theorem B4228271 : Blo 1670035 4228271 := bstep (se 1 (by rfl) ⟨3171203, by rfl⟩ : syracuseStep 4228271 = 6342407) B6342407
theorem B5637383 : Blo 1670035 5637383 := bstep (se 1 (by rfl) ⟨4228037, by rfl⟩ : syracuseStep 5637383 = 8456075) B8456075
theorem B10708271 : Blo 1670035 10708271 := bstep (se 1 (by rfl) ⟨8031203, by rfl⟩ : syracuseStep 10708271 = 16062407) B16062407
theorem B25101635 : Blo 1670035 25101635 := bstep (se 1 (by rfl) ⟨18826226, by rfl⟩ : syracuseStep 25101635 = 37652453) B37652453
theorem B3761639 : Blo 1670035 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B9520649 : Blo 1670035 9520649 := bstep (se 2 (by rfl) ⟨3570243, by rfl⟩ : syracuseStep 9520649 = 7140487) B7140487
theorem B2819657 : Blo 1670035 2819657 := bstep (se 2 (by rfl) ⟨1057371, by rfl⟩ : syracuseStep 2819657 = 2114743) B2114743
theorem B7137001 : Blo 1670035 7137001 := bstep (se 2 (by rfl) ⟨2676375, by rfl⟩ : syracuseStep 7137001 = 5352751) B5352751
theorem B5351521 : Blo 1670035 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B2820217 : Blo 1670035 2820217 := bstep (se 2 (by rfl) ⟨1057581, by rfl⟩ : syracuseStep 2820217 = 2115163) B2115163
theorem B4229243 : Blo 1670035 4229243 := bstep (se 1 (by rfl) ⟨3171932, by rfl⟩ : syracuseStep 4229243 = 6343865) B6343865
theorem B6342907 : Blo 1670035 6342907 := bstep (se 1 (by rfl) ⟨4757180, by rfl⟩ : syracuseStep 6342907 = 9514361) B9514361
theorem B5638463 : Blo 1670035 5638463 := bstep (se 1 (by rfl) ⟨4228847, by rfl⟩ : syracuseStep 5638463 = 8457695) B8457695
theorem B12683627 : Blo 1670035 12683627 := bstep (se 1 (by rfl) ⟨9512720, by rfl⟩ : syracuseStep 12683627 = 19025441) B19025441
theorem B115820923 : Blo 1670035 115820923 := bstep (se 1 (by rfl) ⟨86865692, by rfl⟩ : syracuseStep 115820923 = 173731385) B173731385
theorem B42830207 : Blo 1670035 42830207 := bstep (se 1 (by rfl) ⟨32122655, by rfl⟩ : syracuseStep 42830207 = 64245311) B64245311
theorem B2378431 : Blo 1670035 2378431 := bstep (se 1 (by rfl) ⟨1783823, by rfl⟩ : syracuseStep 2378431 = 3567647) B3567647
theorem B1878907 : Blo 1670035 1878907 := bstep (se 1 (by rfl) ⟨1409180, by rfl⟩ : syracuseStep 1878907 = 2818361) B2818361
theorem B45738917 : Blo 1670035 45738917 := bstep (se 4 (by rfl) ⟨4288023, by rfl⟩ : syracuseStep 45738917 = 8576047) B8576047
theorem B5639273 : Blo 1670035 5639273 := bstep (se 2 (by rfl) ⟨2114727, by rfl⟩ : syracuseStep 5639273 = 4229455) B4229455
theorem B20606251 : Blo 1670035 20606251 := bstep (se 1 (by rfl) ⟨15454688, by rfl⟩ : syracuseStep 20606251 = 30909377) B30909377
theorem B12684599 : Blo 1670035 12684599 := bstep (se 1 (by rfl) ⟨9513449, by rfl⟩ : syracuseStep 12684599 = 19026899) B19026899
theorem B5082905 : Blo 1670035 5082905 := bstep (se 2 (by rfl) ⟨1906089, by rfl⟩ : syracuseStep 5082905 = 3812179) B3812179
theorem B8032031 : Blo 1670035 8032031 := bstep (se 1 (by rfl) ⟨6024023, by rfl⟩ : syracuseStep 8032031 = 12048047) B12048047
theorem B8572759 : Blo 1670035 8572759 := bstep (se 1 (by rfl) ⟨6429569, by rfl⟩ : syracuseStep 8572759 = 12859139) B12859139
theorem B3174241 : Blo 1670035 3174241 := bstep (se 2 (by rfl) ⟨1190340, by rfl⟩ : syracuseStep 3174241 = 2380681) B2380681
theorem B6344639 : Blo 1670035 6344639 := bstep (se 1 (by rfl) ⟨4758479, by rfl⟩ : syracuseStep 6344639 = 9516959) B9516959
theorem B5640731 : Blo 1670035 5640731 := bstep (se 1 (by rfl) ⟨4230548, by rfl⟩ : syracuseStep 5640731 = 8461097) B8461097
theorem B11432729 : Blo 1670035 11432729 := bstep (se 2 (by rfl) ⟨4287273, by rfl⟩ : syracuseStep 11432729 = 8574547) B8574547
theorem B12694319 : Blo 1670035 12694319 := bstep (se 1 (by rfl) ⟨9520739, by rfl⟩ : syracuseStep 12694319 = 19041479) B19041479
theorem B4756315 : Blo 1670035 4756315 := bstep (se 1 (by rfl) ⟨3567236, by rfl⟩ : syracuseStep 4756315 = 7134473) B7134473
theorem B4232027 : Blo 1670035 4232027 := bstep (se 1 (by rfl) ⟨3174020, by rfl⟩ : syracuseStep 4232027 = 6348041) B6348041
theorem B4756715 : Blo 1670035 4756715 := bstep (se 1 (by rfl) ⟨3567536, by rfl⟩ : syracuseStep 4756715 = 7135073) B7135073
theorem B34289243 : Blo 1670035 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B3757679 : Blo 1670035 3757679 := bstep (se 1 (by rfl) ⟨2818259, by rfl⟩ : syracuseStep 3757679 = 5636519) B5636519
theorem B5642351 : Blo 1670035 5642351 := bstep (se 1 (by rfl) ⟨4231763, by rfl⟩ : syracuseStep 5642351 = 8463527) B8463527
theorem B12687515 : Blo 1670035 12687515 := bstep (se 1 (by rfl) ⟨9515636, by rfl⟩ : syracuseStep 12687515 = 19031273) B19031273
theorem B3758363 : Blo 1670035 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B20896037 : Blo 1670035 20896037 := bstep (se 4 (by rfl) ⟨1959003, by rfl⟩ : syracuseStep 20896037 = 3918007) B3918007
theorem B6609377 : Blo 1670035 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B4758047 : Blo 1670035 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B2505311 : Blo 1670035 2505311 := bstep (se 1 (by rfl) ⟨1878983, by rfl⟩ : syracuseStep 2505311 = 3757967) B3757967
theorem B1784575 : Blo 1670035 1784575 := bstep (se 1 (by rfl) ⟨1338431, by rfl⟩ : syracuseStep 1784575 = 2676863) B2676863
theorem B14269355 : Blo 1670035 14269355 := bstep (se 1 (by rfl) ⟨10702016, by rfl⟩ : syracuseStep 14269355 = 21404033) B21404033
theorem B1670127 : Blo 1670035 1670127 := bstep (se 1 (by rfl) ⟨1252595, by rfl⟩ : syracuseStep 1670127 = 2505191) B2505191
theorem B1694747 : Blo 1670035 1694747 := bstep (se 1 (by rfl) ⟨1271060, by rfl⟩ : syracuseStep 1694747 = 2542121) B2542121
theorem B1670175 : Blo 1670035 1670175 := bstep (se 1 (by rfl) ⟨1252631, by rfl⟩ : syracuseStep 1670175 = 2505263) B2505263
theorem B2505791 : Blo 1670035 2505791 := bstep (se 1 (by rfl) ⟨1879343, by rfl⟩ : syracuseStep 2505791 = 3758687) B3758687
theorem B15449287 : Blo 1670035 15449287 := bstep (se 1 (by rfl) ⟨11586965, by rfl⟩ : syracuseStep 15449287 = 23173931) B23173931
theorem B3759335 : Blo 1670035 3759335 := bstep (se 1 (by rfl) ⟨2819501, by rfl⟩ : syracuseStep 3759335 = 5639003) B5639003
theorem B7134439 : Blo 1670035 7134439 := bstep (se 1 (by rfl) ⟨5350829, by rfl⟩ : syracuseStep 7134439 = 10701659) B10701659
theorem B6348071 : Blo 1670035 6348071 := bstep (se 1 (by rfl) ⟨4761053, by rfl⟩ : syracuseStep 6348071 = 9522107) B9522107
theorem B2506139 : Blo 1670035 2506139 := bstep (se 1 (by rfl) ⟨1879604, by rfl⟩ : syracuseStep 2506139 = 3759209) B3759209
theorem B1670623 : Blo 1670035 1670623 := bstep (se 1 (by rfl) ⟨1252967, by rfl⟩ : syracuseStep 1670623 = 2505935) B2505935
theorem B1670683 : Blo 1670035 1670683 := bstep (se 1 (by rfl) ⟨1253012, by rfl⟩ : syracuseStep 1670683 = 2506025) B2506025
theorem B1670703 : Blo 1670035 1670703 := bstep (se 1 (by rfl) ⟨1253027, by rfl⟩ : syracuseStep 1670703 = 2506055) B2506055
theorem B15244847 : Blo 1670035 15244847 := bstep (se 1 (by rfl) ⟨11433635, by rfl⟩ : syracuseStep 15244847 = 22867271) B22867271
theorem B11583185 : Blo 1670035 11583185 := bstep (se 2 (by rfl) ⟨4343694, by rfl⟩ : syracuseStep 11583185 = 8687389) B8687389
theorem B2506559 : Blo 1670035 2506559 := bstep (se 1 (by rfl) ⟨1879919, by rfl⟩ : syracuseStep 2506559 = 3759839) B3759839
theorem B1671103 : Blo 1670035 1671103 := bstep (se 1 (by rfl) ⟨1253327, by rfl⟩ : syracuseStep 1671103 = 2506655) B2506655
theorem B1671163 : Blo 1670035 1671163 := bstep (se 1 (by rfl) ⟨1253372, by rfl⟩ : syracuseStep 1671163 = 2506745) B2506745
theorem B1671199 : Blo 1670035 1671199 := bstep (se 1 (by rfl) ⟨1253399, by rfl⟩ : syracuseStep 1671199 = 2506799) B2506799
theorem B1671215 : Blo 1670035 1671215 := bstep (se 1 (by rfl) ⟨1253411, by rfl⟩ : syracuseStep 1671215 = 2506823) B2506823
theorem B7135361 : Blo 1670035 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B3760289 : Blo 1670035 3760289 := bstep (se 2 (by rfl) ⟨1410108, by rfl⟩ : syracuseStep 3760289 = 2820217) B2820217
theorem B1671335 : Blo 1670035 1671335 := bstep (se 1 (by rfl) ⟨1253501, by rfl⟩ : syracuseStep 1671335 = 2507003) B2507003
theorem B1671419 : Blo 1670035 1671419 := bstep (se 1 (by rfl) ⟨1253564, by rfl⟩ : syracuseStep 1671419 = 2507129) B2507129
theorem B3760487 : Blo 1670035 3760487 := bstep (se 1 (by rfl) ⟨2820365, by rfl⟩ : syracuseStep 3760487 = 5640731) B5640731
theorem B1671527 : Blo 1670035 1671527 := bstep (se 1 (by rfl) ⟨1253645, by rfl⟩ : syracuseStep 1671527 = 2507291) B2507291
theorem B1671615 : Blo 1670035 1671615 := bstep (se 1 (by rfl) ⟨1253711, by rfl⟩ : syracuseStep 1671615 = 2507423) B2507423
theorem B1671647 : Blo 1670035 1671647 := bstep (se 1 (by rfl) ⟨1253735, by rfl⟩ : syracuseStep 1671647 = 2507471) B2507471
theorem B154427897 : Blo 1670035 154427897 := bstep (se 2 (by rfl) ⟨57910461, by rfl⟩ : syracuseStep 154427897 = 115820923) B115820923
theorem B8462879 : Blo 1670035 8462879 := bstep (se 1 (by rfl) ⟨6347159, by rfl⟩ : syracuseStep 8462879 = 12694319) B12694319
theorem B1671727 : Blo 1670035 1671727 := bstep (se 1 (by rfl) ⟨1253795, by rfl⟩ : syracuseStep 1671727 = 2507591) B2507591
theorem B1671771 : Blo 1670035 1671771 := bstep (se 1 (by rfl) ⟨1253828, by rfl⟩ : syracuseStep 1671771 = 2507657) B2507657
theorem B2818847 : Blo 1670035 2818847 := bstep (se 1 (by rfl) ⟨2114135, by rfl⟩ : syracuseStep 2818847 = 4228271) B4228271
theorem B3171143 : Blo 1670035 3171143 := bstep (se 1 (by rfl) ⟨2378357, by rfl⟩ : syracuseStep 3171143 = 4756715) B4756715
theorem B66937693 : Blo 1670035 66937693 := bstep (se 3 (by rfl) ⟨12550817, by rfl⟩ : syracuseStep 66937693 = 25101635) B25101635
theorem B3171241 : Blo 1670035 3171241 := bstep (se 2 (by rfl) ⟨1189215, by rfl⟩ : syracuseStep 3171241 = 2378431) B2378431
theorem B2507759 : Blo 1670035 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B6341753 : Blo 1670035 6341753 := bstep (se 2 (by rfl) ⟨2378157, by rfl⟩ : syracuseStep 6341753 = 4756315) B4756315
theorem B3761567 : Blo 1670035 3761567 := bstep (se 1 (by rfl) ⟨2821175, by rfl⟩ : syracuseStep 3761567 = 5642351) B5642351
theorem B2819495 : Blo 1670035 2819495 := bstep (se 1 (by rfl) ⟨2114621, by rfl⟩ : syracuseStep 2819495 = 4229243) B4229243
theorem B8455751 : Blo 1670035 8455751 := bstep (se 1 (by rfl) ⟨6341813, by rfl⟩ : syracuseStep 8455751 = 12683627) B12683627
theorem B9512585 : Blo 1670035 9512585 := bstep (se 2 (by rfl) ⟨3567219, by rfl⟩ : syracuseStep 9512585 = 7134439) B7134439
theorem B3172031 : Blo 1670035 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B45721381 : Blo 1670035 45721381 := bstep (se 4 (by rfl) ⟨4286379, by rfl⟩ : syracuseStep 45721381 = 8572759) B8572759
theorem B30492611 : Blo 1670035 30492611 := bstep (se 1 (by rfl) ⟨22869458, by rfl⟩ : syracuseStep 30492611 = 45738917) B45738917
theorem B9512903 : Blo 1670035 9512903 := bstep (se 1 (by rfl) ⟨7134677, by rfl⟩ : syracuseStep 9512903 = 14269355) B14269355
theorem B123553973 : Blo 1670035 123553973 := bstep (se 5 (by rfl) ⟨5791592, by rfl⟩ : syracuseStep 123553973 = 11583185) B11583185
theorem B8456399 : Blo 1670035 8456399 := bstep (se 1 (by rfl) ⟨6342299, by rfl⟩ : syracuseStep 8456399 = 12684599) B12684599
theorem B4229759 : Blo 1670035 4229759 := bstep (se 1 (by rfl) ⟨3172319, by rfl⟩ : syracuseStep 4229759 = 6344639) B6344639
theorem B8457209 : Blo 1670035 8457209 := bstep (se 2 (by rfl) ⟨3171453, by rfl⟩ : syracuseStep 8457209 = 6342907) B6342907
theorem B7621819 : Blo 1670035 7621819 := bstep (se 1 (by rfl) ⟨5716364, by rfl⟩ : syracuseStep 7621819 = 11432729) B11432729
theorem B72264905 : Blo 1670035 72264905 := bstep (se 2 (by rfl) ⟨27099339, by rfl⟩ : syracuseStep 72264905 = 54198679) B54198679
theorem B2821351 : Blo 1670035 2821351 := bstep (se 1 (by rfl) ⟨2116013, by rfl⟩ : syracuseStep 2821351 = 4232027) B4232027
theorem B7138847 : Blo 1670035 7138847 := bstep (se 1 (by rfl) ⟨5354135, by rfl⟩ : syracuseStep 7138847 = 10708271) B10708271
theorem B1879771 : Blo 1670035 1879771 := bstep (se 1 (by rfl) ⟨1409828, by rfl⟩ : syracuseStep 1879771 = 2819657) B2819657
theorem B22859495 : Blo 1670035 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B8458343 : Blo 1670035 8458343 := bstep (se 1 (by rfl) ⟨6343757, by rfl⟩ : syracuseStep 8458343 = 12687515) B12687515
theorem B891564245 : Blo 1670035 891564245 := bstep (se 7 (by rfl) ⟨10448018, by rfl⟩ : syracuseStep 891564245 = 20896037) B20896037
theorem B28553471 : Blo 1670035 28553471 := bstep (se 1 (by rfl) ⟨21415103, by rfl⟩ : syracuseStep 28553471 = 42830207) B42830207
theorem B20599049 : Blo 1670035 20599049 := bstep (se 2 (by rfl) ⟨7724643, by rfl⟩ : syracuseStep 20599049 = 15449287) B15449287
theorem B4232047 : Blo 1670035 4232047 := bstep (se 1 (by rfl) ⟨3174035, by rfl⟩ : syracuseStep 4232047 = 6348071) B6348071
theorem B9516001 : Blo 1670035 9516001 := bstep (se 2 (by rfl) ⟨3568500, by rfl⟩ : syracuseStep 9516001 = 7137001) B7137001
theorem B10163231 : Blo 1670035 10163231 := bstep (se 1 (by rfl) ⟨7622423, by rfl⟩ : syracuseStep 10163231 = 15244847) B15244847
theorem B4232321 : Blo 1670035 4232321 := bstep (se 2 (by rfl) ⟨1587120, by rfl⟩ : syracuseStep 4232321 = 3174241) B3174241
theorem B3388603 : Blo 1670035 3388603 := bstep (se 1 (by rfl) ⟨2541452, by rfl⟩ : syracuseStep 3388603 = 5082905) B5082905
theorem B5354687 : Blo 1670035 5354687 := bstep (se 1 (by rfl) ⟨4016015, by rfl⟩ : syracuseStep 5354687 = 8032031) B8032031
theorem B4519325 : Blo 1670035 4519325 := bstep (se 3 (by rfl) ⟨847373, by rfl⟩ : syracuseStep 4519325 = 1694747) B1694747
theorem B3758201 : Blo 1670035 3758201 := bstep (se 2 (by rfl) ⟨1409325, by rfl⟩ : syracuseStep 3758201 = 2818651) B2818651
theorem B3758255 : Blo 1670035 3758255 := bstep (se 1 (by rfl) ⟨2818691, by rfl⟩ : syracuseStep 3758255 = 5637383) B5637383
theorem B6347099 : Blo 1670035 6347099 := bstep (se 1 (by rfl) ⟨4760324, by rfl⟩ : syracuseStep 6347099 = 9520649) B9520649
theorem B2505119 : Blo 1670035 2505119 := bstep (se 1 (by rfl) ⟨1878839, by rfl⟩ : syracuseStep 2505119 = 3757679) B3757679
theorem B2505209 : Blo 1670035 2505209 := bstep (se 2 (by rfl) ⟨939453, by rfl⟩ : syracuseStep 2505209 = 1878907) B1878907
theorem B9517733 : Blo 1670035 9517733 := bstep (se 4 (by rfl) ⟨892287, by rfl⟩ : syracuseStep 9517733 = 1784575) B1784575
theorem B2505575 : Blo 1670035 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B8575865 : Blo 1670035 8575865 := bstep (se 2 (by rfl) ⟨3215949, by rfl⟩ : syracuseStep 8575865 = 6431899) B6431899
theorem B3758975 : Blo 1670035 3758975 := bstep (se 1 (by rfl) ⟨2819231, by rfl⟩ : syracuseStep 3758975 = 5638463) B5638463
theorem B4406251 : Blo 1670035 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B27475001 : Blo 1670035 27475001 := bstep (se 2 (by rfl) ⟨10303125, by rfl⟩ : syracuseStep 27475001 = 20606251) B20606251
theorem B1670207 : Blo 1670035 1670207 := bstep (se 1 (by rfl) ⟨1252655, by rfl⟩ : syracuseStep 1670207 = 2505311) B2505311
theorem B1670527 : Blo 1670035 1670527 := bstep (se 1 (by rfl) ⟨1252895, by rfl⟩ : syracuseStep 1670527 = 2505791) B2505791
theorem B3759515 : Blo 1670035 3759515 := bstep (se 1 (by rfl) ⟨2819636, by rfl⟩ : syracuseStep 3759515 = 5639273) B5639273
theorem B2506223 : Blo 1670035 2506223 := bstep (se 1 (by rfl) ⟨1879667, by rfl⟩ : syracuseStep 2506223 = 3759335) B3759335
theorem B1670759 : Blo 1670035 1670759 := bstep (se 1 (by rfl) ⟨1253069, by rfl⟩ : syracuseStep 1670759 = 2506139) B2506139
theorem B1671039 : Blo 1670035 1671039 := bstep (se 1 (by rfl) ⟨1253279, by rfl⟩ : syracuseStep 1671039 = 2506559) B2506559
theorem B2506859 : Blo 1670035 2506859 := bstep (se 1 (by rfl) ⟨1880144, by rfl⟩ : syracuseStep 2506859 = 3760289) B3760289
theorem B2506991 : Blo 1670035 2506991 := bstep (se 1 (by rfl) ⟨1880243, by rfl⟩ : syracuseStep 2506991 = 3760487) B3760487
theorem B14279165 : Blo 1670035 14279165 := bstep (se 3 (by rfl) ⟨2677343, by rfl⟩ : syracuseStep 14279165 = 5354687) B5354687
theorem B2114095 : Blo 1670035 2114095 := bstep (se 1 (by rfl) ⟨1585571, by rfl⟩ : syracuseStep 2114095 = 3171143) B3171143
theorem B1671839 : Blo 1670035 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B6775487 : Blo 1670035 6775487 := bstep (se 1 (by rfl) ⟨5081615, by rfl⟩ : syracuseStep 6775487 = 10163231) B10163231
theorem B4227835 : Blo 1670035 4227835 := bstep (se 1 (by rfl) ⟨3170876, by rfl⟩ : syracuseStep 4227835 = 6341753) B6341753
theorem B2507711 : Blo 1670035 2507711 := bstep (se 1 (by rfl) ⟨1880783, by rfl⟩ : syracuseStep 2507711 = 3761567) B3761567
theorem B40649701 : Blo 1670035 40649701 := bstep (se 4 (by rfl) ⟨3810909, by rfl⟩ : syracuseStep 40649701 = 7621819) B7621819
theorem B5637167 : Blo 1670035 5637167 := bstep (se 1 (by rfl) ⟨4227875, by rfl⟩ : syracuseStep 5637167 = 8455751) B8455751
theorem B6341723 : Blo 1670035 6341723 := bstep (se 1 (by rfl) ⟨4756292, by rfl⟩ : syracuseStep 6341723 = 9512585) B9512585
theorem B2114687 : Blo 1670035 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B4228321 : Blo 1670035 4228321 := bstep (se 2 (by rfl) ⟨1585620, by rfl⟩ : syracuseStep 4228321 = 3171241) B3171241
theorem B6341935 : Blo 1670035 6341935 := bstep (se 1 (by rfl) ⟨4756451, by rfl⟩ : syracuseStep 6341935 = 9512903) B9512903
theorem B5875001 : Blo 1670035 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B5637599 : Blo 1670035 5637599 := bstep (se 1 (by rfl) ⟨4228199, by rfl⟩ : syracuseStep 5637599 = 8456399) B8456399
theorem B3761801 : Blo 1670035 3761801 := bstep (se 2 (by rfl) ⟨1410675, by rfl⟩ : syracuseStep 3761801 = 2821351) B2821351
theorem B2819839 : Blo 1670035 2819839 := bstep (se 1 (by rfl) ⟨2114879, by rfl⟩ : syracuseStep 2819839 = 4229759) B4229759
theorem B5638139 : Blo 1670035 5638139 := bstep (se 1 (by rfl) ⟨4228604, by rfl⟩ : syracuseStep 5638139 = 8457209) B8457209
theorem B15239663 : Blo 1670035 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B5638895 : Blo 1670035 5638895 := bstep (se 1 (by rfl) ⟨4229171, by rfl⟩ : syracuseStep 5638895 = 8458343) B8458343
theorem B1879231 : Blo 1670035 1879231 := bstep (se 1 (by rfl) ⟨1409423, by rfl⟩ : syracuseStep 1879231 = 2818847) B2818847
theorem B54930797 : Blo 1670035 54930797 := bstep (se 3 (by rfl) ⟨10299524, by rfl⟩ : syracuseStep 54930797 = 20599049) B20599049
theorem B2821547 : Blo 1670035 2821547 := bstep (se 1 (by rfl) ⟨2116160, by rfl⟩ : syracuseStep 2821547 = 4232321) B4232321
theorem B1879663 : Blo 1670035 1879663 := bstep (se 1 (by rfl) ⟨1409747, by rfl⟩ : syracuseStep 1879663 = 2819495) B2819495
theorem B20328407 : Blo 1670035 20328407 := bstep (se 1 (by rfl) ⟨15246305, by rfl⟩ : syracuseStep 20328407 = 30492611) B30492611
theorem B411807725 : Blo 1670035 411807725 := bstep (se 3 (by rfl) ⟨77213948, by rfl⟩ : syracuseStep 411807725 = 154427897) B154427897
theorem B4231399 : Blo 1670035 4231399 := bstep (se 1 (by rfl) ⟨3173549, by rfl⟩ : syracuseStep 4231399 = 6347099) B6347099
theorem B4518137 : Blo 1670035 4518137 := bstep (se 2 (by rfl) ⟨1694301, by rfl⟩ : syracuseStep 4518137 = 3388603) B3388603
theorem B6345155 : Blo 1670035 6345155 := bstep (se 1 (by rfl) ⟨4758866, by rfl⟩ : syracuseStep 6345155 = 9517733) B9517733
theorem B60961841 : Blo 1670035 60961841 := bstep (se 2 (by rfl) ⟨22860690, by rfl⟩ : syracuseStep 60961841 = 45721381) B45721381
theorem B4756907 : Blo 1670035 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B594376163 : Blo 1670035 594376163 := bstep (se 1 (by rfl) ⟨445782122, by rfl⟩ : syracuseStep 594376163 = 891564245) B891564245
theorem B19035647 : Blo 1670035 19035647 := bstep (se 1 (by rfl) ⟨14276735, by rfl⟩ : syracuseStep 19035647 = 28553471) B28553471
theorem B5641919 : Blo 1670035 5641919 := bstep (se 1 (by rfl) ⟨4231439, by rfl⟩ : syracuseStep 5641919 = 8462879) B8462879
theorem B3012883 : Blo 1670035 3012883 := bstep (se 1 (by rfl) ⟨2259662, by rfl⟩ : syracuseStep 3012883 = 4519325) B4519325
theorem B89250257 : Blo 1670035 89250257 := bstep (se 2 (by rfl) ⟨33468846, by rfl⟩ : syracuseStep 89250257 = 66937693) B66937693
theorem B5642729 : Blo 1670035 5642729 := bstep (se 2 (by rfl) ⟨2116023, by rfl⟩ : syracuseStep 5642729 = 4232047) B4232047
theorem B12688001 : Blo 1670035 12688001 := bstep (se 2 (by rfl) ⟨4758000, by rfl⟩ : syracuseStep 12688001 = 9516001) B9516001
theorem B2505467 : Blo 1670035 2505467 := bstep (se 1 (by rfl) ⟨1879100, by rfl⟩ : syracuseStep 2505467 = 3758201) B3758201
theorem B2505503 : Blo 1670035 2505503 := bstep (se 1 (by rfl) ⟨1879127, by rfl⟩ : syracuseStep 2505503 = 3758255) B3758255
theorem B82369315 : Blo 1670035 82369315 := bstep (se 1 (by rfl) ⟨61776986, by rfl⟩ : syracuseStep 82369315 = 123553973) B123553973
theorem B1670079 : Blo 1670035 1670079 := bstep (se 1 (by rfl) ⟨1252559, by rfl⟩ : syracuseStep 1670079 = 2505119) B2505119
theorem B1670139 : Blo 1670035 1670139 := bstep (se 1 (by rfl) ⟨1252604, by rfl⟩ : syracuseStep 1670139 = 2505209) B2505209
theorem B1670383 : Blo 1670035 1670383 := bstep (se 1 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 1670383 = 2505575) B2505575
theorem B5717243 : Blo 1670035 5717243 := bstep (se 1 (by rfl) ⟨4287932, by rfl⟩ : syracuseStep 5717243 = 8575865) B8575865
theorem B2505983 : Blo 1670035 2505983 := bstep (se 1 (by rfl) ⟨1879487, by rfl⟩ : syracuseStep 2505983 = 3758975) B3758975
theorem B18316667 : Blo 1670035 18316667 := bstep (se 1 (by rfl) ⟨13737500, by rfl⟩ : syracuseStep 18316667 = 27475001) B27475001
theorem B48176603 : Blo 1670035 48176603 := bstep (se 1 (by rfl) ⟨36132452, by rfl⟩ : syracuseStep 48176603 = 72264905) B72264905
theorem B2506343 : Blo 1670035 2506343 := bstep (se 1 (by rfl) ⟨1879757, by rfl⟩ : syracuseStep 2506343 = 3759515) B3759515
theorem B2506361 : Blo 1670035 2506361 := bstep (se 2 (by rfl) ⟨939885, by rfl⟩ : syracuseStep 2506361 = 1879771) B1879771
theorem B1670815 : Blo 1670035 1670815 := bstep (se 1 (by rfl) ⟨1253111, by rfl⟩ : syracuseStep 1670815 = 2506223) B2506223
theorem B4759231 : Blo 1670035 4759231 := bstep (se 1 (by rfl) ⟨3569423, by rfl⟩ : syracuseStep 4759231 = 7138847) B7138847
theorem B1671239 : Blo 1670035 1671239 := bstep (se 1 (by rfl) ⟨1253429, by rfl⟩ : syracuseStep 1671239 = 2506859) B2506859
theorem B1671327 : Blo 1670035 1671327 := bstep (se 1 (by rfl) ⟨1253495, by rfl⟩ : syracuseStep 1671327 = 2506991) B2506991
theorem B9519443 : Blo 1670035 9519443 := bstep (se 1 (by rfl) ⟨7139582, by rfl⟩ : syracuseStep 9519443 = 14279165) B14279165
theorem B1671807 : Blo 1670035 1671807 := bstep (se 1 (by rfl) ⟨1253855, by rfl⟩ : syracuseStep 1671807 = 2507711) B2507711
theorem B40641227 : Blo 1670035 40641227 := bstep (se 1 (by rfl) ⟨30480920, by rfl⟩ : syracuseStep 40641227 = 60961841) B60961841
theorem B4227815 : Blo 1670035 4227815 := bstep (se 1 (by rfl) ⟨3170861, by rfl⟩ : syracuseStep 4227815 = 6341723) B6341723
theorem B2818793 : Blo 1670035 2818793 := bstep (se 2 (by rfl) ⟨1057047, by rfl⟩ : syracuseStep 2818793 = 2114095) B2114095
theorem B3916667 : Blo 1670035 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B5637113 : Blo 1670035 5637113 := bstep (se 2 (by rfl) ⟨2113917, by rfl⟩ : syracuseStep 5637113 = 4227835) B4227835
theorem B12690431 : Blo 1670035 12690431 := bstep (se 1 (by rfl) ⟨9517823, by rfl⟩ : syracuseStep 12690431 = 19035647) B19035647
theorem B2507867 : Blo 1670035 2507867 := bstep (se 1 (by rfl) ⟨1880900, by rfl⟩ : syracuseStep 2507867 = 3761801) B3761801
theorem B3761279 : Blo 1670035 3761279 := bstep (se 1 (by rfl) ⟨2820959, by rfl⟩ : syracuseStep 3761279 = 5641919) B5641919
theorem B54199601 : Blo 1670035 54199601 := bstep (se 2 (by rfl) ⟨20324850, by rfl⟩ : syracuseStep 54199601 = 40649701) B40649701
theorem B5637761 : Blo 1670035 5637761 := bstep (se 2 (by rfl) ⟨2114160, by rfl⟩ : syracuseStep 5637761 = 4228321) B4228321
theorem B59500171 : Blo 1670035 59500171 := bstep (se 1 (by rfl) ⟨44625128, by rfl⟩ : syracuseStep 59500171 = 89250257) B89250257
theorem B3761819 : Blo 1670035 3761819 := bstep (se 1 (by rfl) ⟨2821364, by rfl⟩ : syracuseStep 3761819 = 5642729) B5642729
theorem B10159775 : Blo 1670035 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B8455913 : Blo 1670035 8455913 := bstep (se 2 (by rfl) ⟨3170967, by rfl⟩ : syracuseStep 8455913 = 6341935) B6341935
theorem B3811495 : Blo 1670035 3811495 := bstep (se 1 (by rfl) ⟨2858621, by rfl⟩ : syracuseStep 3811495 = 5717243) B5717243
theorem B36620531 : Blo 1670035 36620531 := bstep (se 1 (by rfl) ⟨27465398, by rfl⟩ : syracuseStep 36620531 = 54930797) B54930797
theorem B13552271 : Blo 1670035 13552271 := bstep (se 1 (by rfl) ⟨10164203, by rfl⟩ : syracuseStep 13552271 = 20328407) B20328407
theorem B4230103 : Blo 1670035 4230103 := bstep (se 1 (by rfl) ⟨3172577, by rfl⟩ : syracuseStep 4230103 = 6345155) B6345155
theorem B5639165 : Blo 1670035 5639165 := bstep (se 3 (by rfl) ⟨1057343, by rfl⟩ : syracuseStep 5639165 = 2114687) B2114687
theorem B4516991 : Blo 1670035 4516991 := bstep (se 1 (by rfl) ⟨3387743, by rfl⟩ : syracuseStep 4516991 = 6775487) B6775487
theorem B396250775 : Blo 1670035 396250775 := bstep (se 1 (by rfl) ⟨297188081, by rfl⟩ : syracuseStep 396250775 = 594376163) B594376163
theorem B109825753 : Blo 1670035 109825753 := bstep (se 2 (by rfl) ⟨41184657, by rfl⟩ : syracuseStep 109825753 = 82369315) B82369315
theorem B12685085 : Blo 1670035 12685085 := bstep (se 3 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 12685085 = 4756907) B4756907
theorem B16068709 : Blo 1670035 16068709 := bstep (se 4 (by rfl) ⟨1506441, by rfl⟩ : syracuseStep 16068709 = 3012883) B3012883
theorem B8458667 : Blo 1670035 8458667 := bstep (se 1 (by rfl) ⟨6344000, by rfl⟩ : syracuseStep 8458667 = 12688001) B12688001
theorem B12211111 : Blo 1670035 12211111 := bstep (se 1 (by rfl) ⟨9158333, by rfl⟩ : syracuseStep 12211111 = 18316667) B18316667
theorem B6345641 : Blo 1670035 6345641 := bstep (se 2 (by rfl) ⟨2379615, by rfl⟩ : syracuseStep 6345641 = 4759231) B4759231
theorem B1881031 : Blo 1670035 1881031 := bstep (se 1 (by rfl) ⟨1410773, by rfl⟩ : syracuseStep 1881031 = 2821547) B2821547
theorem B32117735 : Blo 1670035 32117735 := bstep (se 1 (by rfl) ⟨24088301, by rfl⟩ : syracuseStep 32117735 = 48176603) B48176603
theorem B5641865 : Blo 1670035 5641865 := bstep (se 2 (by rfl) ⟨2115699, by rfl⟩ : syracuseStep 5641865 = 4231399) B4231399
theorem B12048365 : Blo 1670035 12048365 := bstep (se 3 (by rfl) ⟨2259068, by rfl⟩ : syracuseStep 12048365 = 4518137) B4518137
theorem B3758111 : Blo 1670035 3758111 := bstep (se 1 (by rfl) ⟨2818583, by rfl⟩ : syracuseStep 3758111 = 5637167) B5637167
theorem B3758399 : Blo 1670035 3758399 := bstep (se 1 (by rfl) ⟨2818799, by rfl⟩ : syracuseStep 3758399 = 5637599) B5637599
theorem B3758759 : Blo 1670035 3758759 := bstep (se 1 (by rfl) ⟨2819069, by rfl⟩ : syracuseStep 3758759 = 5638139) B5638139
theorem B2505641 : Blo 1670035 2505641 := bstep (se 2 (by rfl) ⟨939615, by rfl⟩ : syracuseStep 2505641 = 1879231) B1879231
theorem B3759263 : Blo 1670035 3759263 := bstep (se 1 (by rfl) ⟨2819447, by rfl⟩ : syracuseStep 3759263 = 5638895) B5638895
theorem B1670311 : Blo 1670035 1670311 := bstep (se 1 (by rfl) ⟨1252733, by rfl⟩ : syracuseStep 1670311 = 2505467) B2505467
theorem B1670335 : Blo 1670035 1670335 := bstep (se 1 (by rfl) ⟨1252751, by rfl⟩ : syracuseStep 1670335 = 2505503) B2505503
theorem B2506217 : Blo 1670035 2506217 := bstep (se 2 (by rfl) ⟨939831, by rfl⟩ : syracuseStep 2506217 = 1879663) B1879663
theorem B1670655 : Blo 1670035 1670655 := bstep (se 1 (by rfl) ⟨1252991, by rfl⟩ : syracuseStep 1670655 = 2505983) B2505983
theorem B3759785 : Blo 1670035 3759785 := bstep (se 2 (by rfl) ⟨1409919, by rfl⟩ : syracuseStep 3759785 = 2819839) B2819839
theorem B1670895 : Blo 1670035 1670895 := bstep (se 1 (by rfl) ⟨1253171, by rfl⟩ : syracuseStep 1670895 = 2506343) B2506343
theorem B1670907 : Blo 1670035 1670907 := bstep (se 1 (by rfl) ⟨1253180, by rfl⟩ : syracuseStep 1670907 = 2506361) B2506361
theorem B274538483 : Blo 1670035 274538483 := bstep (se 1 (by rfl) ⟨205903862, by rfl⟩ : syracuseStep 274538483 = 411807725) B411807725
theorem B2818543 : Blo 1670035 2818543 := bstep (se 1 (by rfl) ⟨2113907, by rfl⟩ : syracuseStep 2818543 = 4227815) B4227815
theorem B1671911 : Blo 1670035 1671911 := bstep (se 1 (by rfl) ⟨1253933, by rfl⟩ : syracuseStep 1671911 = 2507867) B2507867
theorem B2507519 : Blo 1670035 2507519 := bstep (se 1 (by rfl) ⟨1880639, by rfl⟩ : syracuseStep 2507519 = 3761279) B3761279
theorem B3761243 : Blo 1670035 3761243 := bstep (se 1 (by rfl) ⟨2820932, by rfl⟩ : syracuseStep 3761243 = 5641865) B5641865
theorem B2507879 : Blo 1670035 2507879 := bstep (se 1 (by rfl) ⟨1880909, by rfl⟩ : syracuseStep 2507879 = 3761819) B3761819
theorem B5637275 : Blo 1670035 5637275 := bstep (se 1 (by rfl) ⟨4227956, by rfl⟩ : syracuseStep 5637275 = 8455913) B8455913
theorem B2508041 : Blo 1670035 2508041 := bstep (se 2 (by rfl) ⟨940515, by rfl⟩ : syracuseStep 2508041 = 1881031) B1881031
theorem B183025655 : Blo 1670035 183025655 := bstep (se 1 (by rfl) ⟨137269241, by rfl⟩ : syracuseStep 183025655 = 274538483) B274538483
theorem B24413687 : Blo 1670035 24413687 := bstep (se 1 (by rfl) ⟨18310265, by rfl⟩ : syracuseStep 24413687 = 36620531) B36620531
theorem B79333561 : Blo 1670035 79333561 := bstep (se 2 (by rfl) ⟨29750085, by rfl⟩ : syracuseStep 79333561 = 59500171) B59500171
theorem B146434337 : Blo 1670035 146434337 := bstep (se 2 (by rfl) ⟨54912876, by rfl⟩ : syracuseStep 146434337 = 109825753) B109825753
theorem B8456723 : Blo 1670035 8456723 := bstep (se 1 (by rfl) ⟨6342542, by rfl⟩ : syracuseStep 8456723 = 12685085) B12685085
theorem B21424945 : Blo 1670035 21424945 := bstep (se 2 (by rfl) ⟨8034354, by rfl⟩ : syracuseStep 21424945 = 16068709) B16068709
theorem B5081993 : Blo 1670035 5081993 := bstep (se 2 (by rfl) ⟨1905747, by rfl⟩ : syracuseStep 5081993 = 3811495) B3811495
theorem B5639111 : Blo 1670035 5639111 := bstep (se 1 (by rfl) ⟨4229333, by rfl⟩ : syracuseStep 5639111 = 8458667) B8458667
theorem B27094151 : Blo 1670035 27094151 := bstep (se 1 (by rfl) ⟨20320613, by rfl⟩ : syracuseStep 27094151 = 40641227) B40641227
theorem B1879195 : Blo 1670035 1879195 := bstep (se 1 (by rfl) ⟨1409396, by rfl⟩ : syracuseStep 1879195 = 2818793) B2818793
theorem B4230427 : Blo 1670035 4230427 := bstep (se 1 (by rfl) ⟨3172820, by rfl⟩ : syracuseStep 4230427 = 6345641) B6345641
theorem B16281481 : Blo 1670035 16281481 := bstep (se 2 (by rfl) ⟨6105555, by rfl⟩ : syracuseStep 16281481 = 12211111) B12211111
theorem B5640137 : Blo 1670035 5640137 := bstep (se 2 (by rfl) ⟨2115051, by rfl⟩ : syracuseStep 5640137 = 4230103) B4230103
theorem B8032243 : Blo 1670035 8032243 := bstep (se 1 (by rfl) ⟨6024182, by rfl⟩ : syracuseStep 8032243 = 12048365) B12048365
theorem B3011327 : Blo 1670035 3011327 := bstep (se 1 (by rfl) ⟨2258495, by rfl⟩ : syracuseStep 3011327 = 4516991) B4516991
theorem B6346295 : Blo 1670035 6346295 := bstep (se 1 (by rfl) ⟨4759721, by rfl⟩ : syracuseStep 6346295 = 9519443) B9519443
theorem B2611111 : Blo 1670035 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B21411823 : Blo 1670035 21411823 := bstep (se 1 (by rfl) ⟨16058867, by rfl⟩ : syracuseStep 21411823 = 32117735) B32117735
theorem B3758075 : Blo 1670035 3758075 := bstep (se 1 (by rfl) ⟨2818556, by rfl⟩ : syracuseStep 3758075 = 5637113) B5637113
theorem B8460287 : Blo 1670035 8460287 := bstep (se 1 (by rfl) ⟨6345215, by rfl⟩ : syracuseStep 8460287 = 12690431) B12690431
theorem B36133067 : Blo 1670035 36133067 := bstep (se 1 (by rfl) ⟨27099800, by rfl⟩ : syracuseStep 36133067 = 54199601) B54199601
theorem B3758507 : Blo 1670035 3758507 := bstep (se 1 (by rfl) ⟨2818880, by rfl⟩ : syracuseStep 3758507 = 5637761) B5637761
theorem B6773183 : Blo 1670035 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B2505407 : Blo 1670035 2505407 := bstep (se 1 (by rfl) ⟨1879055, by rfl⟩ : syracuseStep 2505407 = 3758111) B3758111
theorem B2505599 : Blo 1670035 2505599 := bstep (se 1 (by rfl) ⟨1879199, by rfl⟩ : syracuseStep 2505599 = 3758399) B3758399
theorem B9034847 : Blo 1670035 9034847 := bstep (se 1 (by rfl) ⟨6776135, by rfl⟩ : syracuseStep 9034847 = 13552271) B13552271
theorem B2505839 : Blo 1670035 2505839 := bstep (se 1 (by rfl) ⟨1879379, by rfl⟩ : syracuseStep 2505839 = 3758759) B3758759
theorem B1670427 : Blo 1670035 1670427 := bstep (se 1 (by rfl) ⟨1252820, by rfl⟩ : syracuseStep 1670427 = 2505641) B2505641
theorem B3759443 : Blo 1670035 3759443 := bstep (se 1 (by rfl) ⟨2819582, by rfl⟩ : syracuseStep 3759443 = 5639165) B5639165
theorem B2506175 : Blo 1670035 2506175 := bstep (se 1 (by rfl) ⟨1879631, by rfl⟩ : syracuseStep 2506175 = 3759263) B3759263
theorem B1670811 : Blo 1670035 1670811 := bstep (se 1 (by rfl) ⟨1253108, by rfl⟩ : syracuseStep 1670811 = 2506217) B2506217
theorem B264167183 : Blo 1670035 264167183 := bstep (se 1 (by rfl) ⟨198125387, by rfl⟩ : syracuseStep 264167183 = 396250775) B396250775
theorem B2506523 : Blo 1670035 2506523 := bstep (se 1 (by rfl) ⟨1879892, by rfl⟩ : syracuseStep 2506523 = 3759785) B3759785
theorem B2007551 : Blo 1670035 2007551 := bstep (se 1 (by rfl) ⟨1505663, by rfl⟩ : syracuseStep 2007551 = 3011327) B3011327
theorem B1671679 : Blo 1670035 1671679 := bstep (se 1 (by rfl) ⟨1253759, by rfl⟩ : syracuseStep 1671679 = 2507519) B2507519
theorem B2507495 : Blo 1670035 2507495 := bstep (se 1 (by rfl) ⟨1880621, by rfl⟩ : syracuseStep 2507495 = 3761243) B3761243
theorem B1671919 : Blo 1670035 1671919 := bstep (se 1 (by rfl) ⟨1253939, by rfl⟩ : syracuseStep 1671919 = 2507879) B2507879
theorem B1672027 : Blo 1670035 1672027 := bstep (se 1 (by rfl) ⟨1254020, by rfl⟩ : syracuseStep 1672027 = 2508041) B2508041
theorem B28566593 : Blo 1670035 28566593 := bstep (se 2 (by rfl) ⟨10712472, by rfl⟩ : syracuseStep 28566593 = 21424945) B21424945
theorem B4515455 : Blo 1670035 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B5637815 : Blo 1670035 5637815 := bstep (se 1 (by rfl) ⟨4228361, by rfl⟩ : syracuseStep 5637815 = 8456723) B8456723
theorem B6023231 : Blo 1670035 6023231 := bstep (se 1 (by rfl) ⟨4517423, by rfl⟩ : syracuseStep 6023231 = 9034847) B9034847
theorem B10709657 : Blo 1670035 10709657 := bstep (se 2 (by rfl) ⟨4016121, by rfl⟩ : syracuseStep 10709657 = 8032243) B8032243
theorem B105778081 : Blo 1670035 105778081 := bstep (se 2 (by rfl) ⟨39666780, by rfl⟩ : syracuseStep 105778081 = 79333561) B79333561
theorem B4230863 : Blo 1670035 4230863 := bstep (se 1 (by rfl) ⟨3173147, by rfl⟩ : syracuseStep 4230863 = 6346295) B6346295
theorem B5640191 : Blo 1670035 5640191 := bstep (se 1 (by rfl) ⟨4230143, by rfl⟩ : syracuseStep 5640191 = 8460287) B8460287
theorem B24088711 : Blo 1670035 24088711 := bstep (se 1 (by rfl) ⟨18066533, by rfl⟩ : syracuseStep 24088711 = 36133067) B36133067
theorem B5640569 : Blo 1670035 5640569 := bstep (se 2 (by rfl) ⟨2115213, by rfl⟩ : syracuseStep 5640569 = 4230427) B4230427
theorem B3387995 : Blo 1670035 3387995 := bstep (se 1 (by rfl) ⟨2540996, by rfl⟩ : syracuseStep 3387995 = 5081993) B5081993
theorem B122017103 : Blo 1670035 122017103 := bstep (se 1 (by rfl) ⟨91512827, by rfl⟩ : syracuseStep 122017103 = 183025655) B183025655
theorem B3758057 : Blo 1670035 3758057 := bstep (se 2 (by rfl) ⟨1409271, by rfl⟩ : syracuseStep 3758057 = 2818543) B2818543
theorem B3758183 : Blo 1670035 3758183 := bstep (se 1 (by rfl) ⟨2818637, by rfl⟩ : syracuseStep 3758183 = 5637275) B5637275
theorem B16275791 : Blo 1670035 16275791 := bstep (se 1 (by rfl) ⟨12206843, by rfl⟩ : syracuseStep 16275791 = 24413687) B24413687
theorem B2505383 : Blo 1670035 2505383 := bstep (se 1 (by rfl) ⟨1879037, by rfl⟩ : syracuseStep 2505383 = 3758075) B3758075
theorem B97622891 : Blo 1670035 97622891 := bstep (se 1 (by rfl) ⟨73217168, by rfl⟩ : syracuseStep 97622891 = 146434337) B146434337
theorem B2505593 : Blo 1670035 2505593 := bstep (se 2 (by rfl) ⟨939597, by rfl⟩ : syracuseStep 2505593 = 1879195) B1879195
theorem B2505671 : Blo 1670035 2505671 := bstep (se 1 (by rfl) ⟨1879253, by rfl⟩ : syracuseStep 2505671 = 3758507) B3758507
theorem B1670271 : Blo 1670035 1670271 := bstep (se 1 (by rfl) ⟨1252703, by rfl⟩ : syracuseStep 1670271 = 2505407) B2505407
theorem B1670399 : Blo 1670035 1670399 := bstep (se 1 (by rfl) ⟨1252799, by rfl⟩ : syracuseStep 1670399 = 2505599) B2505599
theorem B3759407 : Blo 1670035 3759407 := bstep (se 1 (by rfl) ⟨2819555, by rfl⟩ : syracuseStep 3759407 = 5639111) B5639111
theorem B1670559 : Blo 1670035 1670559 := bstep (se 1 (by rfl) ⟨1252919, by rfl⟩ : syracuseStep 1670559 = 2505839) B2505839
theorem B18062767 : Blo 1670035 18062767 := bstep (se 1 (by rfl) ⟨13547075, by rfl⟩ : syracuseStep 18062767 = 27094151) B27094151
theorem B2506295 : Blo 1670035 2506295 := bstep (se 1 (by rfl) ⟨1879721, by rfl⟩ : syracuseStep 2506295 = 3759443) B3759443
theorem B1670783 : Blo 1670035 1670783 := bstep (se 1 (by rfl) ⟨1253087, by rfl⟩ : syracuseStep 1670783 = 2506175) B2506175
theorem B21708641 : Blo 1670035 21708641 := bstep (se 2 (by rfl) ⟨8140740, by rfl⟩ : syracuseStep 21708641 = 16281481) B16281481
theorem B176111455 : Blo 1670035 176111455 := bstep (se 1 (by rfl) ⟨132083591, by rfl⟩ : syracuseStep 176111455 = 264167183) B264167183
theorem B1671015 : Blo 1670035 1671015 := bstep (se 1 (by rfl) ⟨1253261, by rfl⟩ : syracuseStep 1671015 = 2506523) B2506523
theorem B3481481 : Blo 1670035 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B3760091 : Blo 1670035 3760091 := bstep (se 1 (by rfl) ⟨2820068, by rfl⟩ : syracuseStep 3760091 = 5640137) B5640137
theorem B28549097 : Blo 1670035 28549097 := bstep (se 2 (by rfl) ⟨10705911, by rfl⟩ : syracuseStep 28549097 = 21411823) B21411823
theorem B3760379 : Blo 1670035 3760379 := bstep (se 1 (by rfl) ⟨2820284, by rfl⟩ : syracuseStep 3760379 = 5640569) B5640569
theorem B1671663 : Blo 1670035 1671663 := bstep (se 1 (by rfl) ⟨1253747, by rfl⟩ : syracuseStep 1671663 = 2507495) B2507495
theorem B4015487 : Blo 1670035 4015487 := bstep (se 1 (by rfl) ⟨3011615, by rfl⟩ : syracuseStep 4015487 = 6023231) B6023231
theorem B9283949 : Blo 1670035 9283949 := bstep (se 3 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 9283949 = 3481481) B3481481
theorem B2820575 : Blo 1670035 2820575 := bstep (se 1 (by rfl) ⟨2115431, by rfl⟩ : syracuseStep 2820575 = 4230863) B4230863
theorem B19032731 : Blo 1670035 19032731 := bstep (se 1 (by rfl) ⟨14274548, by rfl⟩ : syracuseStep 19032731 = 28549097) B28549097
theorem B3760127 : Blo 1670035 3760127 := bstep (se 1 (by rfl) ⟨2820095, by rfl⟩ : syracuseStep 3760127 = 5640191) B5640191
theorem B3010303 : Blo 1670035 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B5353469 : Blo 1670035 5353469 := bstep (se 3 (by rfl) ⟨1003775, by rfl⟩ : syracuseStep 5353469 = 2007551) B2007551
theorem B10850527 : Blo 1670035 10850527 := bstep (se 1 (by rfl) ⟨8137895, by rfl⟩ : syracuseStep 10850527 = 16275791) B16275791
theorem B7139771 : Blo 1670035 7139771 := bstep (se 1 (by rfl) ⟨5354828, by rfl⟩ : syracuseStep 7139771 = 10709657) B10709657
theorem B65081927 : Blo 1670035 65081927 := bstep (se 1 (by rfl) ⟨48811445, by rfl⟩ : syracuseStep 65081927 = 97622891) B97622891
theorem B14472427 : Blo 1670035 14472427 := bstep (se 1 (by rfl) ⟨10854320, by rfl⟩ : syracuseStep 14472427 = 21708641) B21708641
theorem B32118281 : Blo 1670035 32118281 := bstep (se 2 (by rfl) ⟨12044355, by rfl⟩ : syracuseStep 32118281 = 24088711) B24088711
theorem B2258663 : Blo 1670035 2258663 := bstep (se 1 (by rfl) ⟨1693997, by rfl⟩ : syracuseStep 2258663 = 3387995) B3387995
theorem B19044395 : Blo 1670035 19044395 := bstep (se 1 (by rfl) ⟨14283296, by rfl⟩ : syracuseStep 19044395 = 28566593) B28566593
theorem B81344735 : Blo 1670035 81344735 := bstep (se 1 (by rfl) ⟨61008551, by rfl⟩ : syracuseStep 81344735 = 122017103) B122017103
theorem B3758543 : Blo 1670035 3758543 := bstep (se 1 (by rfl) ⟨2818907, by rfl⟩ : syracuseStep 3758543 = 5637815) B5637815
theorem B2505371 : Blo 1670035 2505371 := bstep (se 1 (by rfl) ⟨1879028, by rfl⟩ : syracuseStep 2505371 = 3758057) B3758057
theorem B2505455 : Blo 1670035 2505455 := bstep (se 1 (by rfl) ⟨1879091, by rfl⟩ : syracuseStep 2505455 = 3758183) B3758183
theorem B1670255 : Blo 1670035 1670255 := bstep (se 1 (by rfl) ⟨1252691, by rfl⟩ : syracuseStep 1670255 = 2505383) B2505383
theorem B24083689 : Blo 1670035 24083689 := bstep (se 2 (by rfl) ⟨9031383, by rfl⟩ : syracuseStep 24083689 = 18062767) B18062767
theorem B1670395 : Blo 1670035 1670395 := bstep (se 1 (by rfl) ⟨1252796, by rfl⟩ : syracuseStep 1670395 = 2505593) B2505593
theorem B1670447 : Blo 1670035 1670447 := bstep (se 1 (by rfl) ⟨1252835, by rfl⟩ : syracuseStep 1670447 = 2505671) B2505671
theorem B564149765 : Blo 1670035 564149765 := bstep (se 4 (by rfl) ⟨52889040, by rfl⟩ : syracuseStep 564149765 = 105778081) B105778081
theorem B2506271 : Blo 1670035 2506271 := bstep (se 1 (by rfl) ⟨1879703, by rfl⟩ : syracuseStep 2506271 = 3759407) B3759407
theorem B1670863 : Blo 1670035 1670863 := bstep (se 1 (by rfl) ⟨1253147, by rfl⟩ : syracuseStep 1670863 = 2506295) B2506295
theorem B234815273 : Blo 1670035 234815273 := bstep (se 2 (by rfl) ⟨88055727, by rfl⟩ : syracuseStep 234815273 = 176111455) B176111455
theorem B2506727 : Blo 1670035 2506727 := bstep (se 1 (by rfl) ⟨1880045, by rfl⟩ : syracuseStep 2506727 = 3760091) B3760091
theorem B2506919 : Blo 1670035 2506919 := bstep (se 1 (by rfl) ⟨1880189, by rfl⟩ : syracuseStep 2506919 = 3760379) B3760379
theorem B4759847 : Blo 1670035 4759847 := bstep (se 1 (by rfl) ⟨3569885, by rfl⟩ : syracuseStep 4759847 = 7139771) B7139771
theorem B14467369 : Blo 1670035 14467369 := bstep (se 2 (by rfl) ⟨5425263, by rfl⟩ : syracuseStep 14467369 = 10850527) B10850527
theorem B6023101 : Blo 1670035 6023101 := bstep (se 3 (by rfl) ⟨1129331, by rfl⟩ : syracuseStep 6023101 = 2258663) B2258663
theorem B156543515 : Blo 1670035 156543515 := bstep (se 1 (by rfl) ⟨117407636, by rfl⟩ : syracuseStep 156543515 = 234815273) B234815273
theorem B173551805 : Blo 1670035 173551805 := bstep (se 3 (by rfl) ⟨32540963, by rfl⟩ : syracuseStep 173551805 = 65081927) B65081927
theorem B6189299 : Blo 1670035 6189299 := bstep (se 1 (by rfl) ⟨4641974, by rfl⟩ : syracuseStep 6189299 = 9283949) B9283949
theorem B19296569 : Blo 1670035 19296569 := bstep (se 2 (by rfl) ⟨7236213, by rfl⟩ : syracuseStep 19296569 = 14472427) B14472427
theorem B1880383 : Blo 1670035 1880383 := bstep (se 1 (by rfl) ⟨1410287, by rfl⟩ : syracuseStep 1880383 = 2820575) B2820575
theorem B2506751 : Blo 1670035 2506751 := bstep (se 1 (by rfl) ⟨1880063, by rfl⟩ : syracuseStep 2506751 = 3760127) B3760127
theorem B376099843 : Blo 1670035 376099843 := bstep (se 1 (by rfl) ⟨282074882, by rfl⟩ : syracuseStep 376099843 = 564149765) B564149765
theorem B3568979 : Blo 1670035 3568979 := bstep (se 1 (by rfl) ⟨2676734, by rfl⟩ : syracuseStep 3568979 = 5353469) B5353469
theorem B2676991 : Blo 1670035 2676991 := bstep (se 1 (by rfl) ⟨2007743, by rfl⟩ : syracuseStep 2676991 = 4015487) B4015487
theorem B21412187 : Blo 1670035 21412187 := bstep (se 1 (by rfl) ⟨16059140, by rfl⟩ : syracuseStep 21412187 = 32118281) B32118281
theorem B16054949 : Blo 1670035 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B12696263 : Blo 1670035 12696263 := bstep (se 1 (by rfl) ⟨9522197, by rfl⟩ : syracuseStep 12696263 = 19044395) B19044395
theorem B54229823 : Blo 1670035 54229823 := bstep (se 1 (by rfl) ⟨40672367, by rfl⟩ : syracuseStep 54229823 = 81344735) B81344735
theorem B2505695 : Blo 1670035 2505695 := bstep (se 1 (by rfl) ⟨1879271, by rfl⟩ : syracuseStep 2505695 = 3758543) B3758543
theorem B32111585 : Blo 1670035 32111585 := bstep (se 2 (by rfl) ⟨12041844, by rfl⟩ : syracuseStep 32111585 = 24083689) B24083689
theorem B1670247 : Blo 1670035 1670247 := bstep (se 1 (by rfl) ⟨1252685, by rfl⟩ : syracuseStep 1670247 = 2505371) B2505371
theorem B12688487 : Blo 1670035 12688487 := bstep (se 1 (by rfl) ⟨9516365, by rfl⟩ : syracuseStep 12688487 = 19032731) B19032731
theorem B1670303 : Blo 1670035 1670303 := bstep (se 1 (by rfl) ⟨1252727, by rfl⟩ : syracuseStep 1670303 = 2505455) B2505455
theorem B1670847 : Blo 1670035 1670847 := bstep (se 1 (by rfl) ⟨1253135, by rfl⟩ : syracuseStep 1670847 = 2506271) B2506271
theorem B1671151 : Blo 1670035 1671151 := bstep (se 1 (by rfl) ⟨1253363, by rfl⟩ : syracuseStep 1671151 = 2506727) B2506727
theorem B1671279 : Blo 1670035 1671279 := bstep (se 1 (by rfl) ⟨1253459, by rfl⟩ : syracuseStep 1671279 = 2506919) B2506919
theorem B2507177 : Blo 1670035 2507177 := bstep (se 2 (by rfl) ⟨940191, by rfl⟩ : syracuseStep 2507177 = 1880383) B1880383
theorem B501466457 : Blo 1670035 501466457 := bstep (se 2 (by rfl) ⟨188049921, by rfl⟩ : syracuseStep 501466457 = 376099843) B376099843
theorem B8464175 : Blo 1670035 8464175 := bstep (se 1 (by rfl) ⟨6348131, by rfl⟩ : syracuseStep 8464175 = 12696263) B12696263
theorem B36153215 : Blo 1670035 36153215 := bstep (se 1 (by rfl) ⟨27114911, by rfl⟩ : syracuseStep 36153215 = 54229823) B54229823
theorem B21407723 : Blo 1670035 21407723 := bstep (se 1 (by rfl) ⟨16055792, by rfl⟩ : syracuseStep 21407723 = 32111585) B32111585
theorem B8030801 : Blo 1670035 8030801 := bstep (se 2 (by rfl) ⟨3011550, by rfl⟩ : syracuseStep 8030801 = 6023101) B6023101
theorem B3173231 : Blo 1670035 3173231 := bstep (se 1 (by rfl) ⟨2379923, by rfl⟩ : syracuseStep 3173231 = 4759847) B4759847
theorem B12864379 : Blo 1670035 12864379 := bstep (se 1 (by rfl) ⟨9648284, by rfl⟩ : syracuseStep 12864379 = 19296569) B19296569
theorem B14274791 : Blo 1670035 14274791 := bstep (se 1 (by rfl) ⟨10706093, by rfl⟩ : syracuseStep 14274791 = 21412187) B21412187
theorem B104362343 : Blo 1670035 104362343 := bstep (se 1 (by rfl) ⟨78271757, by rfl⟩ : syracuseStep 104362343 = 156543515) B156543515
theorem B10703299 : Blo 1670035 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B8458991 : Blo 1670035 8458991 := bstep (se 1 (by rfl) ⟨6344243, by rfl⟩ : syracuseStep 8458991 = 12688487) B12688487
theorem B115701203 : Blo 1670035 115701203 := bstep (se 1 (by rfl) ⟨86775902, by rfl⟩ : syracuseStep 115701203 = 173551805) B173551805
theorem B4126199 : Blo 1670035 4126199 := bstep (se 1 (by rfl) ⟨3094649, by rfl⟩ : syracuseStep 4126199 = 6189299) B6189299
theorem B3569321 : Blo 1670035 3569321 := bstep (se 2 (by rfl) ⟨1338495, by rfl⟩ : syracuseStep 3569321 = 2676991) B2676991
theorem B19289825 : Blo 1670035 19289825 := bstep (se 2 (by rfl) ⟨7233684, by rfl⟩ : syracuseStep 19289825 = 14467369) B14467369
theorem B9517277 : Blo 1670035 9517277 := bstep (se 3 (by rfl) ⟨1784489, by rfl⟩ : syracuseStep 9517277 = 3568979) B3568979
theorem B1670463 : Blo 1670035 1670463 := bstep (se 1 (by rfl) ⟨1252847, by rfl⟩ : syracuseStep 1670463 = 2505695) B2505695
theorem B1671167 : Blo 1670035 1671167 := bstep (se 1 (by rfl) ⟨1253375, by rfl⟩ : syracuseStep 1671167 = 2506751) B2506751
theorem B69574895 : Blo 1670035 69574895 := bstep (se 1 (by rfl) ⟨52181171, by rfl⟩ : syracuseStep 69574895 = 104362343) B104362343
theorem B1671451 : Blo 1670035 1671451 := bstep (se 1 (by rfl) ⟨1253588, by rfl⟩ : syracuseStep 1671451 = 2507177) B2507177
theorem B14271065 : Blo 1670035 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B24102143 : Blo 1670035 24102143 := bstep (se 1 (by rfl) ⟨18076607, by rfl⟩ : syracuseStep 24102143 = 36153215) B36153215
theorem B14271815 : Blo 1670035 14271815 := bstep (se 1 (by rfl) ⟨10703861, by rfl⟩ : syracuseStep 14271815 = 21407723) B21407723
theorem B2115487 : Blo 1670035 2115487 := bstep (se 1 (by rfl) ⟨1586615, by rfl⟩ : syracuseStep 2115487 = 3173231) B3173231
theorem B5639327 : Blo 1670035 5639327 := bstep (se 1 (by rfl) ⟨4229495, by rfl⟩ : syracuseStep 5639327 = 8458991) B8458991
theorem B334310971 : Blo 1670035 334310971 := bstep (se 1 (by rfl) ⟨250733228, by rfl⟩ : syracuseStep 334310971 = 501466457) B501466457
theorem B2379547 : Blo 1670035 2379547 := bstep (se 1 (by rfl) ⟨1784660, by rfl⟩ : syracuseStep 2379547 = 3569321) B3569321
theorem B6344851 : Blo 1670035 6344851 := bstep (se 1 (by rfl) ⟨4758638, by rfl⟩ : syracuseStep 6344851 = 9517277) B9517277
theorem B5353867 : Blo 1670035 5353867 := bstep (se 1 (by rfl) ⟨4015400, by rfl⟩ : syracuseStep 5353867 = 8030801) B8030801
theorem B44012789 : Blo 1670035 44012789 := bstep (se 5 (by rfl) ⟨2063099, by rfl⟩ : syracuseStep 44012789 = 4126199) B4126199
theorem B9516527 : Blo 1670035 9516527 := bstep (se 1 (by rfl) ⟨7137395, by rfl⟩ : syracuseStep 9516527 = 14274791) B14274791
theorem B77134135 : Blo 1670035 77134135 := bstep (se 1 (by rfl) ⟨57850601, by rfl⟩ : syracuseStep 77134135 = 115701203) B115701203
theorem B12859883 : Blo 1670035 12859883 := bstep (se 1 (by rfl) ⟨9644912, by rfl⟩ : syracuseStep 12859883 = 19289825) B19289825
theorem B17152505 : Blo 1670035 17152505 := bstep (se 2 (by rfl) ⟨6432189, by rfl⟩ : syracuseStep 17152505 = 12864379) B12864379
theorem B5642783 : Blo 1670035 5642783 := bstep (se 1 (by rfl) ⟨4232087, by rfl⟩ : syracuseStep 5642783 = 8464175) B8464175
theorem B46383263 : Blo 1670035 46383263 := bstep (se 1 (by rfl) ⟨34787447, by rfl⟩ : syracuseStep 46383263 = 69574895) B69574895
theorem B12690917 : Blo 1670035 12690917 := bstep (se 4 (by rfl) ⟨1189773, by rfl⟩ : syracuseStep 12690917 = 2379547) B2379547
theorem B3761855 : Blo 1670035 3761855 := bstep (se 1 (by rfl) ⟨2821391, by rfl⟩ : syracuseStep 3761855 = 5642783) B5642783
theorem B2820649 : Blo 1670035 2820649 := bstep (se 2 (by rfl) ⟨1057743, by rfl⟩ : syracuseStep 2820649 = 2115487) B2115487
theorem B9514043 : Blo 1670035 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B102845513 : Blo 1670035 102845513 := bstep (se 2 (by rfl) ⟨38567067, by rfl⟩ : syracuseStep 102845513 = 77134135) B77134135
theorem B7138489 : Blo 1670035 7138489 := bstep (se 2 (by rfl) ⟨2676933, by rfl⟩ : syracuseStep 7138489 = 5353867) B5353867
theorem B16068095 : Blo 1670035 16068095 := bstep (se 1 (by rfl) ⟨12051071, by rfl⟩ : syracuseStep 16068095 = 24102143) B24102143
theorem B9514543 : Blo 1670035 9514543 := bstep (se 1 (by rfl) ⟨7135907, by rfl⟩ : syracuseStep 9514543 = 14271815) B14271815
theorem B6344351 : Blo 1670035 6344351 := bstep (se 1 (by rfl) ⟨4758263, by rfl⟩ : syracuseStep 6344351 = 9516527) B9516527
theorem B8573255 : Blo 1670035 8573255 := bstep (se 1 (by rfl) ⟨6429941, by rfl⟩ : syracuseStep 8573255 = 12859883) B12859883
theorem B445747961 : Blo 1670035 445747961 := bstep (se 2 (by rfl) ⟨167155485, by rfl⟩ : syracuseStep 445747961 = 334310971) B334310971
theorem B8459801 : Blo 1670035 8459801 := bstep (se 2 (by rfl) ⟨3172425, by rfl⟩ : syracuseStep 8459801 = 6344851) B6344851
theorem B29341859 : Blo 1670035 29341859 := bstep (se 1 (by rfl) ⟨22006394, by rfl⟩ : syracuseStep 29341859 = 44012789) B44012789
theorem B11435003 : Blo 1670035 11435003 := bstep (se 1 (by rfl) ⟨8576252, by rfl⟩ : syracuseStep 11435003 = 17152505) B17152505
theorem B3759551 : Blo 1670035 3759551 := bstep (se 1 (by rfl) ⟨2819663, by rfl⟩ : syracuseStep 3759551 = 5639327) B5639327
theorem B297165307 : Blo 1670035 297165307 := bstep (se 1 (by rfl) ⟨222873980, by rfl⟩ : syracuseStep 297165307 = 445747961) B445747961
theorem B3760865 : Blo 1670035 3760865 := bstep (se 2 (by rfl) ⟨1410324, by rfl⟩ : syracuseStep 3760865 = 2820649) B2820649
theorem B2507903 : Blo 1670035 2507903 := bstep (se 1 (by rfl) ⟨1880927, by rfl⟩ : syracuseStep 2507903 = 3761855) B3761855
theorem B6342695 : Blo 1670035 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B4229567 : Blo 1670035 4229567 := bstep (se 1 (by rfl) ⟨3172175, by rfl⟩ : syracuseStep 4229567 = 6344351) B6344351
theorem B78244957 : Blo 1670035 78244957 := bstep (se 3 (by rfl) ⟨14670929, by rfl⟩ : syracuseStep 78244957 = 29341859) B29341859
theorem B5639867 : Blo 1670035 5639867 := bstep (se 1 (by rfl) ⟨4229900, by rfl⟩ : syracuseStep 5639867 = 8459801) B8459801
theorem B7623335 : Blo 1670035 7623335 := bstep (se 1 (by rfl) ⟨5717501, by rfl⟩ : syracuseStep 7623335 = 11435003) B11435003
theorem B68563675 : Blo 1670035 68563675 := bstep (se 1 (by rfl) ⟨51422756, by rfl⟩ : syracuseStep 68563675 = 102845513) B102845513
theorem B12686057 : Blo 1670035 12686057 := bstep (se 2 (by rfl) ⟨4757271, by rfl⟩ : syracuseStep 12686057 = 9514543) B9514543
theorem B10712063 : Blo 1670035 10712063 := bstep (se 1 (by rfl) ⟨8034047, by rfl⟩ : syracuseStep 10712063 = 16068095) B16068095
theorem B30922175 : Blo 1670035 30922175 := bstep (se 1 (by rfl) ⟨23191631, by rfl⟩ : syracuseStep 30922175 = 46383263) B46383263
theorem B5715503 : Blo 1670035 5715503 := bstep (se 1 (by rfl) ⟨4286627, by rfl⟩ : syracuseStep 5715503 = 8573255) B8573255
theorem B8460611 : Blo 1670035 8460611 := bstep (se 1 (by rfl) ⟨6345458, by rfl⟩ : syracuseStep 8460611 = 12690917) B12690917
theorem B9517985 : Blo 1670035 9517985 := bstep (se 2 (by rfl) ⟨3569244, by rfl⟩ : syracuseStep 9517985 = 7138489) B7138489
theorem B2506367 : Blo 1670035 2506367 := bstep (se 1 (by rfl) ⟨1879775, by rfl⟩ : syracuseStep 2506367 = 3759551) B3759551
theorem B2507243 : Blo 1670035 2507243 := bstep (se 1 (by rfl) ⟨1880432, by rfl⟩ : syracuseStep 2507243 = 3760865) B3760865
theorem B1671935 : Blo 1670035 1671935 := bstep (se 1 (by rfl) ⟨1253951, by rfl⟩ : syracuseStep 1671935 = 2507903) B2507903
theorem B3810335 : Blo 1670035 3810335 := bstep (se 1 (by rfl) ⟨2857751, by rfl⟩ : syracuseStep 3810335 = 5715503) B5715503
theorem B4228463 : Blo 1670035 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B2819711 : Blo 1670035 2819711 := bstep (se 1 (by rfl) ⟨2114783, by rfl⟩ : syracuseStep 2819711 = 4229567) B4229567
theorem B8457371 : Blo 1670035 8457371 := bstep (se 1 (by rfl) ⟨6343028, by rfl⟩ : syracuseStep 8457371 = 12686057) B12686057
theorem B91418233 : Blo 1670035 91418233 := bstep (se 2 (by rfl) ⟨34281837, by rfl⟩ : syracuseStep 91418233 = 68563675) B68563675
theorem B20614783 : Blo 1670035 20614783 := bstep (se 1 (by rfl) ⟨15461087, by rfl⟩ : syracuseStep 20614783 = 30922175) B30922175
theorem B5640407 : Blo 1670035 5640407 := bstep (se 1 (by rfl) ⟨4230305, by rfl⟩ : syracuseStep 5640407 = 8460611) B8460611
theorem B20328893 : Blo 1670035 20328893 := bstep (se 3 (by rfl) ⟨3811667, by rfl⟩ : syracuseStep 20328893 = 7623335) B7623335
theorem B6345323 : Blo 1670035 6345323 := bstep (se 1 (by rfl) ⟨4758992, by rfl⟩ : syracuseStep 6345323 = 9517985) B9517985
theorem B417306437 : Blo 1670035 417306437 := bstep (se 4 (by rfl) ⟨39122478, by rfl⟩ : syracuseStep 417306437 = 78244957) B78244957
theorem B396220409 : Blo 1670035 396220409 := bstep (se 2 (by rfl) ⟨148582653, by rfl⟩ : syracuseStep 396220409 = 297165307) B297165307
theorem B7141375 : Blo 1670035 7141375 := bstep (se 1 (by rfl) ⟨5356031, by rfl⟩ : syracuseStep 7141375 = 10712063) B10712063
theorem B1670911 : Blo 1670035 1670911 := bstep (se 1 (by rfl) ⟨1253183, by rfl⟩ : syracuseStep 1670911 = 2506367) B2506367
theorem B3759911 : Blo 1670035 3759911 := bstep (se 1 (by rfl) ⟨2819933, by rfl⟩ : syracuseStep 3759911 = 5639867) B5639867
theorem B3760271 : Blo 1670035 3760271 := bstep (se 1 (by rfl) ⟨2820203, by rfl⟩ : syracuseStep 3760271 = 5640407) B5640407
theorem B1671495 : Blo 1670035 1671495 := bstep (se 1 (by rfl) ⟨1253621, by rfl⟩ : syracuseStep 1671495 = 2507243) B2507243
theorem B2818975 : Blo 1670035 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B5638247 : Blo 1670035 5638247 := bstep (se 1 (by rfl) ⟨4228685, by rfl⟩ : syracuseStep 5638247 = 8457371) B8457371
theorem B121890977 : Blo 1670035 121890977 := bstep (se 2 (by rfl) ⟨45709116, by rfl⟩ : syracuseStep 121890977 = 91418233) B91418233
theorem B27486377 : Blo 1670035 27486377 := bstep (se 2 (by rfl) ⟨10307391, by rfl⟩ : syracuseStep 27486377 = 20614783) B20614783
theorem B9521833 : Blo 1670035 9521833 := bstep (se 2 (by rfl) ⟨3570687, by rfl⟩ : syracuseStep 9521833 = 7141375) B7141375
theorem B10160893 : Blo 1670035 10160893 := bstep (se 3 (by rfl) ⟨1905167, by rfl⟩ : syracuseStep 10160893 = 3810335) B3810335
theorem B13552595 : Blo 1670035 13552595 := bstep (se 1 (by rfl) ⟨10164446, by rfl⟩ : syracuseStep 13552595 = 20328893) B20328893
theorem B4230215 : Blo 1670035 4230215 := bstep (se 1 (by rfl) ⟨3172661, by rfl⟩ : syracuseStep 4230215 = 6345323) B6345323
theorem B1879807 : Blo 1670035 1879807 := bstep (se 1 (by rfl) ⟨1409855, by rfl⟩ : syracuseStep 1879807 = 2819711) B2819711
theorem B278204291 : Blo 1670035 278204291 := bstep (se 1 (by rfl) ⟨208653218, by rfl⟩ : syracuseStep 278204291 = 417306437) B417306437
theorem B264146939 : Blo 1670035 264146939 := bstep (se 1 (by rfl) ⟨198110204, by rfl⟩ : syracuseStep 264146939 = 396220409) B396220409
theorem B2506607 : Blo 1670035 2506607 := bstep (se 1 (by rfl) ⟨1879955, by rfl⟩ : syracuseStep 2506607 = 3759911) B3759911
theorem B2506847 : Blo 1670035 2506847 := bstep (se 1 (by rfl) ⟨1880135, by rfl⟩ : syracuseStep 2506847 = 3760271) B3760271
theorem B2820143 : Blo 1670035 2820143 := bstep (se 1 (by rfl) ⟨2115107, by rfl⟩ : syracuseStep 2820143 = 4230215) B4230215
theorem B185469527 : Blo 1670035 185469527 := bstep (se 1 (by rfl) ⟨139102145, by rfl⟩ : syracuseStep 185469527 = 278204291) B278204291
theorem B176097959 : Blo 1670035 176097959 := bstep (se 1 (by rfl) ⟨132073469, by rfl⟩ : syracuseStep 176097959 = 264146939) B264146939
theorem B81260651 : Blo 1670035 81260651 := bstep (se 1 (by rfl) ⟨60945488, by rfl⟩ : syracuseStep 81260651 = 121890977) B121890977
theorem B12695777 : Blo 1670035 12695777 := bstep (se 2 (by rfl) ⟨4760916, by rfl⟩ : syracuseStep 12695777 = 9521833) B9521833
theorem B13547857 : Blo 1670035 13547857 := bstep (se 2 (by rfl) ⟨5080446, by rfl⟩ : syracuseStep 13547857 = 10160893) B10160893
theorem B3758633 : Blo 1670035 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B3758831 : Blo 1670035 3758831 := bstep (se 1 (by rfl) ⟨2819123, by rfl⟩ : syracuseStep 3758831 = 5638247) B5638247
theorem B18324251 : Blo 1670035 18324251 := bstep (se 1 (by rfl) ⟨13743188, by rfl⟩ : syracuseStep 18324251 = 27486377) B27486377
theorem B9035063 : Blo 1670035 9035063 := bstep (se 1 (by rfl) ⟨6776297, by rfl⟩ : syracuseStep 9035063 = 13552595) B13552595
theorem B2506409 : Blo 1670035 2506409 := bstep (se 2 (by rfl) ⟨939903, by rfl⟩ : syracuseStep 2506409 = 1879807) B1879807
theorem B1671071 : Blo 1670035 1671071 := bstep (se 1 (by rfl) ⟨1253303, by rfl⟩ : syracuseStep 1671071 = 2506607) B2506607
theorem B1671231 : Blo 1670035 1671231 := bstep (se 1 (by rfl) ⟨1253423, by rfl⟩ : syracuseStep 1671231 = 2506847) B2506847
theorem B54173767 : Blo 1670035 54173767 := bstep (se 1 (by rfl) ⟨40630325, by rfl⟩ : syracuseStep 54173767 = 81260651) B81260651
theorem B18063809 : Blo 1670035 18063809 := bstep (se 2 (by rfl) ⟨6773928, by rfl⟩ : syracuseStep 18063809 = 13547857) B13547857
theorem B8463851 : Blo 1670035 8463851 := bstep (se 1 (by rfl) ⟨6347888, by rfl⟩ : syracuseStep 8463851 = 12695777) B12695777
theorem B12216167 : Blo 1670035 12216167 := bstep (se 1 (by rfl) ⟨9162125, by rfl⟩ : syracuseStep 12216167 = 18324251) B18324251
theorem B6023375 : Blo 1670035 6023375 := bstep (se 1 (by rfl) ⟨4517531, by rfl⟩ : syracuseStep 6023375 = 9035063) B9035063
theorem B1880095 : Blo 1670035 1880095 := bstep (se 1 (by rfl) ⟨1410071, by rfl⟩ : syracuseStep 1880095 = 2820143) B2820143
theorem B123646351 : Blo 1670035 123646351 := bstep (se 1 (by rfl) ⟨92734763, by rfl⟩ : syracuseStep 123646351 = 185469527) B185469527
theorem B2505755 : Blo 1670035 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B117398639 : Blo 1670035 117398639 := bstep (se 1 (by rfl) ⟨88048979, by rfl⟩ : syracuseStep 117398639 = 176097959) B176097959
theorem B2505887 : Blo 1670035 2505887 := bstep (se 1 (by rfl) ⟨1879415, by rfl⟩ : syracuseStep 2505887 = 3758831) B3758831
theorem B1670939 : Blo 1670035 1670939 := bstep (se 1 (by rfl) ⟨1253204, by rfl⟩ : syracuseStep 1670939 = 2506409) B2506409
theorem B2506793 : Blo 1670035 2506793 := bstep (se 2 (by rfl) ⟨940047, by rfl⟩ : syracuseStep 2506793 = 1880095) B1880095
theorem B12042539 : Blo 1670035 12042539 := bstep (se 1 (by rfl) ⟨9031904, by rfl⟩ : syracuseStep 12042539 = 18063809) B18063809
theorem B8144111 : Blo 1670035 8144111 := bstep (se 1 (by rfl) ⟨6108083, by rfl⟩ : syracuseStep 8144111 = 12216167) B12216167
theorem B4015583 : Blo 1670035 4015583 := bstep (se 1 (by rfl) ⟨3011687, by rfl⟩ : syracuseStep 4015583 = 6023375) B6023375
theorem B72231689 : Blo 1670035 72231689 := bstep (se 2 (by rfl) ⟨27086883, by rfl⟩ : syracuseStep 72231689 = 54173767) B54173767
theorem B164861801 : Blo 1670035 164861801 := bstep (se 2 (by rfl) ⟨61823175, by rfl⟩ : syracuseStep 164861801 = 123646351) B123646351
theorem B5642567 : Blo 1670035 5642567 := bstep (se 1 (by rfl) ⟨4231925, by rfl⟩ : syracuseStep 5642567 = 8463851) B8463851
theorem B1670503 : Blo 1670035 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B78265759 : Blo 1670035 78265759 := bstep (se 1 (by rfl) ⟨58699319, by rfl⟩ : syracuseStep 78265759 = 117398639) B117398639
theorem B1670591 : Blo 1670035 1670591 := bstep (se 1 (by rfl) ⟨1252943, by rfl⟩ : syracuseStep 1670591 = 2505887) B2505887
theorem B1671195 : Blo 1670035 1671195 := bstep (se 1 (by rfl) ⟨1253396, by rfl⟩ : syracuseStep 1671195 = 2506793) B2506793
theorem B8028359 : Blo 1670035 8028359 := bstep (se 1 (by rfl) ⟨6021269, by rfl⟩ : syracuseStep 8028359 = 12042539) B12042539
theorem B21717629 : Blo 1670035 21717629 := bstep (se 3 (by rfl) ⟨4072055, by rfl⟩ : syracuseStep 21717629 = 8144111) B8144111
theorem B3761711 : Blo 1670035 3761711 := bstep (se 1 (by rfl) ⟨2821283, by rfl⟩ : syracuseStep 3761711 = 5642567) B5642567
theorem B48154459 : Blo 1670035 48154459 := bstep (se 1 (by rfl) ⟨36115844, by rfl⟩ : syracuseStep 48154459 = 72231689) B72231689
theorem B109907867 : Blo 1670035 109907867 := bstep (se 1 (by rfl) ⟨82430900, by rfl⟩ : syracuseStep 109907867 = 164861801) B164861801
theorem B104354345 : Blo 1670035 104354345 := bstep (se 2 (by rfl) ⟨39132879, by rfl⟩ : syracuseStep 104354345 = 78265759) B78265759
theorem B2677055 : Blo 1670035 2677055 := bstep (se 1 (by rfl) ⟨2007791, by rfl⟩ : syracuseStep 2677055 = 4015583) B4015583
theorem B2507807 : Blo 1670035 2507807 := bstep (se 1 (by rfl) ⟨1880855, by rfl⟩ : syracuseStep 2507807 = 3761711) B3761711
theorem B73271911 : Blo 1670035 73271911 := bstep (se 1 (by rfl) ⟨54953933, by rfl⟩ : syracuseStep 73271911 = 109907867) B109907867
theorem B5352239 : Blo 1670035 5352239 := bstep (se 1 (by rfl) ⟨4014179, by rfl⟩ : syracuseStep 5352239 = 8028359) B8028359
theorem B69569563 : Blo 1670035 69569563 := bstep (se 1 (by rfl) ⟨52177172, by rfl⟩ : syracuseStep 69569563 = 104354345) B104354345
theorem B14478419 : Blo 1670035 14478419 := bstep (se 1 (by rfl) ⟨10858814, by rfl⟩ : syracuseStep 14478419 = 21717629) B21717629
theorem B7138813 : Blo 1670035 7138813 := bstep (se 3 (by rfl) ⟨1338527, by rfl⟩ : syracuseStep 7138813 = 2677055) B2677055
theorem B64205945 : Blo 1670035 64205945 := bstep (se 2 (by rfl) ⟨24077229, by rfl⟩ : syracuseStep 64205945 = 48154459) B48154459
theorem B1671871 : Blo 1670035 1671871 := bstep (se 1 (by rfl) ⟨1253903, by rfl⟩ : syracuseStep 1671871 = 2507807) B2507807
theorem B42803963 : Blo 1670035 42803963 := bstep (se 1 (by rfl) ⟨32102972, by rfl⟩ : syracuseStep 42803963 = 64205945) B64205945
theorem B92759417 : Blo 1670035 92759417 := bstep (se 2 (by rfl) ⟨34784781, by rfl⟩ : syracuseStep 92759417 = 69569563) B69569563
theorem B9652279 : Blo 1670035 9652279 := bstep (se 1 (by rfl) ⟨7239209, by rfl⟩ : syracuseStep 9652279 = 14478419) B14478419
theorem B3568159 : Blo 1670035 3568159 := bstep (se 1 (by rfl) ⟨2676119, by rfl⟩ : syracuseStep 3568159 = 5352239) B5352239
theorem B97695881 : Blo 1670035 97695881 := bstep (se 2 (by rfl) ⟨36635955, by rfl⟩ : syracuseStep 97695881 = 73271911) B73271911
theorem B9518417 : Blo 1670035 9518417 := bstep (se 2 (by rfl) ⟨3569406, by rfl⟩ : syracuseStep 9518417 = 7138813) B7138813
theorem B12869705 : Blo 1670035 12869705 := bstep (se 2 (by rfl) ⟨4826139, by rfl⟩ : syracuseStep 12869705 = 9652279) B9652279
theorem B28535975 : Blo 1670035 28535975 := bstep (se 1 (by rfl) ⟨21401981, by rfl⟩ : syracuseStep 28535975 = 42803963) B42803963
theorem B65130587 : Blo 1670035 65130587 := bstep (se 1 (by rfl) ⟨48847940, by rfl⟩ : syracuseStep 65130587 = 97695881) B97695881
theorem B6345611 : Blo 1670035 6345611 := bstep (se 1 (by rfl) ⟨4759208, by rfl⟩ : syracuseStep 6345611 = 9518417) B9518417
theorem B4757545 : Blo 1670035 4757545 := bstep (se 2 (by rfl) ⟨1784079, by rfl⟩ : syracuseStep 4757545 = 3568159) B3568159
theorem B61839611 : Blo 1670035 61839611 := bstep (se 1 (by rfl) ⟨46379708, by rfl⟩ : syracuseStep 61839611 = 92759417) B92759417
theorem B19023983 : Blo 1670035 19023983 := bstep (se 1 (by rfl) ⟨14267987, by rfl⟩ : syracuseStep 19023983 = 28535975) B28535975
theorem B8579803 : Blo 1670035 8579803 := bstep (se 1 (by rfl) ⟨6434852, by rfl⟩ : syracuseStep 8579803 = 12869705) B12869705
theorem B6343393 : Blo 1670035 6343393 := bstep (se 2 (by rfl) ⟨2378772, by rfl⟩ : syracuseStep 6343393 = 4757545) B4757545
theorem B43420391 : Blo 1670035 43420391 := bstep (se 1 (by rfl) ⟨32565293, by rfl⟩ : syracuseStep 43420391 = 65130587) B65130587
theorem B4230407 : Blo 1670035 4230407 := bstep (se 1 (by rfl) ⟨3172805, by rfl⟩ : syracuseStep 4230407 = 6345611) B6345611
theorem B41226407 : Blo 1670035 41226407 := bstep (se 1 (by rfl) ⟨30919805, by rfl⟩ : syracuseStep 41226407 = 61839611) B61839611
theorem B27484271 : Blo 1670035 27484271 := bstep (se 1 (by rfl) ⟨20613203, by rfl⟩ : syracuseStep 27484271 = 41226407) B41226407
theorem B12682655 : Blo 1670035 12682655 := bstep (se 1 (by rfl) ⟨9511991, by rfl⟩ : syracuseStep 12682655 = 19023983) B19023983
theorem B2820271 : Blo 1670035 2820271 := bstep (se 1 (by rfl) ⟨2115203, by rfl⟩ : syracuseStep 2820271 = 4230407) B4230407
theorem B11439737 : Blo 1670035 11439737 := bstep (se 2 (by rfl) ⟨4289901, by rfl⟩ : syracuseStep 11439737 = 8579803) B8579803
theorem B8457857 : Blo 1670035 8457857 := bstep (se 2 (by rfl) ⟨3171696, by rfl⟩ : syracuseStep 8457857 = 6343393) B6343393
theorem B28946927 : Blo 1670035 28946927 := bstep (se 1 (by rfl) ⟨21710195, by rfl⟩ : syracuseStep 28946927 = 43420391) B43420391
theorem B3760361 : Blo 1670035 3760361 := bstep (se 2 (by rfl) ⟨1410135, by rfl⟩ : syracuseStep 3760361 = 2820271) B2820271
theorem B8455103 : Blo 1670035 8455103 := bstep (se 1 (by rfl) ⟨6341327, by rfl⟩ : syracuseStep 8455103 = 12682655) B12682655
theorem B5638571 : Blo 1670035 5638571 := bstep (se 1 (by rfl) ⟨4228928, by rfl⟩ : syracuseStep 5638571 = 8457857) B8457857
theorem B18322847 : Blo 1670035 18322847 := bstep (se 1 (by rfl) ⟨13742135, by rfl⟩ : syracuseStep 18322847 = 27484271) B27484271
theorem B77191805 : Blo 1670035 77191805 := bstep (se 3 (by rfl) ⟨14473463, by rfl⟩ : syracuseStep 77191805 = 28946927) B28946927
theorem B7626491 : Blo 1670035 7626491 := bstep (se 1 (by rfl) ⟨5719868, by rfl⟩ : syracuseStep 7626491 = 11439737) B11439737
theorem B2506907 : Blo 1670035 2506907 := bstep (se 1 (by rfl) ⟨1880180, by rfl⟩ : syracuseStep 2506907 = 3760361) B3760361
theorem B5636735 : Blo 1670035 5636735 := bstep (se 1 (by rfl) ⟨4227551, by rfl⟩ : syracuseStep 5636735 = 8455103) B8455103
theorem B12215231 : Blo 1670035 12215231 := bstep (se 1 (by rfl) ⟨9161423, by rfl⟩ : syracuseStep 12215231 = 18322847) B18322847
theorem B205844813 : Blo 1670035 205844813 := bstep (se 3 (by rfl) ⟨38595902, by rfl⟩ : syracuseStep 205844813 = 77191805) B77191805
theorem B5084327 : Blo 1670035 5084327 := bstep (se 1 (by rfl) ⟨3813245, by rfl⟩ : syracuseStep 5084327 = 7626491) B7626491
theorem B3759047 : Blo 1670035 3759047 := bstep (se 1 (by rfl) ⟨2819285, by rfl⟩ : syracuseStep 3759047 = 5638571) B5638571
theorem B1671271 : Blo 1670035 1671271 := bstep (se 1 (by rfl) ⟨1253453, by rfl⟩ : syracuseStep 1671271 = 2506907) B2506907
theorem B13558205 : Blo 1670035 13558205 := bstep (se 3 (by rfl) ⟨2542163, by rfl⟩ : syracuseStep 13558205 = 5084327) B5084327
theorem B8143487 : Blo 1670035 8143487 := bstep (se 1 (by rfl) ⟨6107615, by rfl⟩ : syracuseStep 8143487 = 12215231) B12215231
theorem B137229875 : Blo 1670035 137229875 := bstep (se 1 (by rfl) ⟨102922406, by rfl⟩ : syracuseStep 137229875 = 205844813) B205844813
theorem B3757823 : Blo 1670035 3757823 := bstep (se 1 (by rfl) ⟨2818367, by rfl⟩ : syracuseStep 3757823 = 5636735) B5636735
theorem B2506031 : Blo 1670035 2506031 := bstep (se 1 (by rfl) ⟨1879523, by rfl⟩ : syracuseStep 2506031 = 3759047) B3759047
theorem B9038803 : Blo 1670035 9038803 := bstep (se 1 (by rfl) ⟨6779102, by rfl⟩ : syracuseStep 9038803 = 13558205) B13558205
theorem B5428991 : Blo 1670035 5428991 := bstep (se 1 (by rfl) ⟨4071743, by rfl⟩ : syracuseStep 5428991 = 8143487) B8143487
theorem B91486583 : Blo 1670035 91486583 := bstep (se 1 (by rfl) ⟨68614937, by rfl⟩ : syracuseStep 91486583 = 137229875) B137229875
theorem B2505215 : Blo 1670035 2505215 := bstep (se 1 (by rfl) ⟨1878911, by rfl⟩ : syracuseStep 2505215 = 3757823) B3757823
theorem B1670687 : Blo 1670035 1670687 := bstep (se 1 (by rfl) ⟨1253015, by rfl⟩ : syracuseStep 1670687 = 2506031) B2506031
theorem B12051737 : Blo 1670035 12051737 := bstep (se 2 (by rfl) ⟨4519401, by rfl⟩ : syracuseStep 12051737 = 9038803) B9038803
theorem B60991055 : Blo 1670035 60991055 := bstep (se 1 (by rfl) ⟨45743291, by rfl⟩ : syracuseStep 60991055 = 91486583) B91486583
theorem B14477309 : Blo 1670035 14477309 := bstep (se 3 (by rfl) ⟨2714495, by rfl⟩ : syracuseStep 14477309 = 5428991) B5428991
theorem B1670143 : Blo 1670035 1670143 := bstep (se 1 (by rfl) ⟨1252607, by rfl⟩ : syracuseStep 1670143 = 2505215) B2505215
theorem B9651539 : Blo 1670035 9651539 := bstep (se 1 (by rfl) ⟨7238654, by rfl⟩ : syracuseStep 9651539 = 14477309) B14477309
theorem B40660703 : Blo 1670035 40660703 := bstep (se 1 (by rfl) ⟨30495527, by rfl⟩ : syracuseStep 40660703 = 60991055) B60991055
theorem B8034491 : Blo 1670035 8034491 := bstep (se 1 (by rfl) ⟨6025868, by rfl⟩ : syracuseStep 8034491 = 12051737) B12051737
theorem B21425309 : Blo 1670035 21425309 := bstep (se 3 (by rfl) ⟨4017245, by rfl⟩ : syracuseStep 21425309 = 8034491) B8034491
theorem B6434359 : Blo 1670035 6434359 := bstep (se 1 (by rfl) ⟨4825769, by rfl⟩ : syracuseStep 6434359 = 9651539) B9651539
theorem B27107135 : Blo 1670035 27107135 := bstep (se 1 (by rfl) ⟨20330351, by rfl⟩ : syracuseStep 27107135 = 40660703) B40660703
theorem B137266325 : Blo 1670035 137266325 := bstep (se 6 (by rfl) ⟨3217179, by rfl⟩ : syracuseStep 137266325 = 6434359) B6434359
theorem B14283539 : Blo 1670035 14283539 := bstep (se 1 (by rfl) ⟨10712654, by rfl⟩ : syracuseStep 14283539 = 21425309) B21425309
theorem B18071423 : Blo 1670035 18071423 := bstep (se 1 (by rfl) ⟨13553567, by rfl⟩ : syracuseStep 18071423 = 27107135) B27107135
theorem B9522359 : Blo 1670035 9522359 := bstep (se 1 (by rfl) ⟨7141769, by rfl⟩ : syracuseStep 9522359 = 14283539) B14283539
theorem B12047615 : Blo 1670035 12047615 := bstep (se 1 (by rfl) ⟨9035711, by rfl⟩ : syracuseStep 12047615 = 18071423) B18071423
theorem B91510883 : Blo 1670035 91510883 := bstep (se 1 (by rfl) ⟨68633162, by rfl⟩ : syracuseStep 91510883 = 137266325) B137266325
theorem B61007255 : Blo 1670035 61007255 := bstep (se 1 (by rfl) ⟨45755441, by rfl⟩ : syracuseStep 61007255 = 91510883) B91510883
theorem B8031743 : Blo 1670035 8031743 := bstep (se 1 (by rfl) ⟨6023807, by rfl⟩ : syracuseStep 8031743 = 12047615) B12047615
theorem B6348239 : Blo 1670035 6348239 := bstep (se 1 (by rfl) ⟨4761179, by rfl⟩ : syracuseStep 6348239 = 9522359) B9522359
theorem B4232159 : Blo 1670035 4232159 := bstep (se 1 (by rfl) ⟨3174119, by rfl⟩ : syracuseStep 4232159 = 6348239) B6348239
theorem B5354495 : Blo 1670035 5354495 := bstep (se 1 (by rfl) ⟨4015871, by rfl⟩ : syracuseStep 5354495 = 8031743) B8031743
theorem B40671503 : Blo 1670035 40671503 := bstep (se 1 (by rfl) ⟨30503627, by rfl⟩ : syracuseStep 40671503 = 61007255) B61007255
theorem B2821439 : Blo 1670035 2821439 := bstep (se 1 (by rfl) ⟨2116079, by rfl⟩ : syracuseStep 2821439 = 4232159) B4232159
theorem B3569663 : Blo 1670035 3569663 := bstep (se 1 (by rfl) ⟨2677247, by rfl⟩ : syracuseStep 3569663 = 5354495) B5354495
theorem B27114335 : Blo 1670035 27114335 := bstep (se 1 (by rfl) ⟨20335751, by rfl⟩ : syracuseStep 27114335 = 40671503) B40671503
theorem B2379775 : Blo 1670035 2379775 := bstep (se 1 (by rfl) ⟨1784831, by rfl⟩ : syracuseStep 2379775 = 3569663) B3569663
theorem B18076223 : Blo 1670035 18076223 := bstep (se 1 (by rfl) ⟨13557167, by rfl⟩ : syracuseStep 18076223 = 27114335) B27114335
theorem B1880959 : Blo 1670035 1880959 := bstep (se 1 (by rfl) ⟨1410719, by rfl⟩ : syracuseStep 1880959 = 2821439) B2821439
theorem B12050815 : Blo 1670035 12050815 := bstep (se 1 (by rfl) ⟨9038111, by rfl⟩ : syracuseStep 12050815 = 18076223) B18076223
theorem B2507945 : Blo 1670035 2507945 := bstep (se 2 (by rfl) ⟨940479, by rfl⟩ : syracuseStep 2507945 = 1880959) B1880959
theorem B3173033 : Blo 1670035 3173033 := bstep (se 2 (by rfl) ⟨1189887, by rfl⟩ : syracuseStep 3173033 = 2379775) B2379775
theorem B1671963 : Blo 1670035 1671963 := bstep (se 1 (by rfl) ⟨1253972, by rfl⟩ : syracuseStep 1671963 = 2507945) B2507945
theorem B16067753 : Blo 1670035 16067753 := bstep (se 2 (by rfl) ⟨6025407, by rfl⟩ : syracuseStep 16067753 = 12050815) B12050815
theorem B8461421 : Blo 1670035 8461421 := bstep (se 3 (by rfl) ⟨1586516, by rfl⟩ : syracuseStep 8461421 = 3173033) B3173033
theorem B5640947 : Blo 1670035 5640947 := bstep (se 1 (by rfl) ⟨4230710, by rfl⟩ : syracuseStep 5640947 = 8461421) B8461421
theorem B10711835 : Blo 1670035 10711835 := bstep (se 1 (by rfl) ⟨8033876, by rfl⟩ : syracuseStep 10711835 = 16067753) B16067753
theorem B3760631 : Blo 1670035 3760631 := bstep (se 1 (by rfl) ⟨2820473, by rfl⟩ : syracuseStep 3760631 = 5640947) B5640947
theorem B7141223 : Blo 1670035 7141223 := bstep (se 1 (by rfl) ⟨5355917, by rfl⟩ : syracuseStep 7141223 = 10711835) B10711835
theorem B2507087 : Blo 1670035 2507087 := bstep (se 1 (by rfl) ⟨1880315, by rfl⟩ : syracuseStep 2507087 = 3760631) B3760631
theorem B4760815 : Blo 1670035 4760815 := bstep (se 1 (by rfl) ⟨3570611, by rfl⟩ : syracuseStep 4760815 = 7141223) B7141223
theorem B1671391 : Blo 1670035 1671391 := bstep (se 1 (by rfl) ⟨1253543, by rfl⟩ : syracuseStep 1671391 = 2507087) B2507087
theorem B6347753 : Blo 1670035 6347753 := bstep (se 2 (by rfl) ⟨2380407, by rfl⟩ : syracuseStep 6347753 = 4760815) B4760815
theorem B4231835 : Blo 1670035 4231835 := bstep (se 1 (by rfl) ⟨3173876, by rfl⟩ : syracuseStep 4231835 = 6347753) B6347753
theorem B2821223 : Blo 1670035 2821223 := bstep (se 1 (by rfl) ⟨2115917, by rfl⟩ : syracuseStep 2821223 = 4231835) B4231835
theorem B1880815 : Blo 1670035 1880815 := bstep (se 1 (by rfl) ⟨1410611, by rfl⟩ : syracuseStep 1880815 = 2821223) B2821223
theorem B2507753 : Blo 1670035 2507753 := bstep (se 2 (by rfl) ⟨940407, by rfl⟩ : syracuseStep 2507753 = 1880815) B1880815
theorem B1671835 : Blo 1670035 1671835 := bstep (se 1 (by rfl) ⟨1253876, by rfl⟩ : syracuseStep 1671835 = 2507753) B2507753

theorem C0 (j : ℕ) (h1 : 417508 ≤ j) (h2 : j ≤ 418008) : Blo 1670035 (4 * j + 3) := by
  interval_cases j
  · exact B1670035
  · exact B1670039
  · exact B1670043
  · exact B1670047
  · exact B1670051
  · exact B1670055
  · exact B1670059
  · exact B1670063
  · exact B1670067
  · exact B1670071
  · exact B1670075
  · exact B1670079
  · exact B1670083
  · exact B1670087
  · exact B1670091
  · exact B1670095
  · exact B1670099
  · exact B1670103
  · exact B1670107
  · exact B1670111
  · exact B1670115
  · exact B1670119
  · exact B1670123
  · exact B1670127
  · exact B1670131
  · exact B1670135
  · exact B1670139
  · exact B1670143
  · exact B1670147
  · exact B1670151
  · exact B1670155
  · exact B1670159
  · exact B1670163
  · exact B1670167
  · exact B1670171
  · exact B1670175
  · exact B1670179
  · exact B1670183
  · exact B1670187
  · exact B1670191
  · exact B1670195
  · exact B1670199
  · exact B1670203
  · exact B1670207
  · exact B1670211
  · exact B1670215
  · exact B1670219
  · exact B1670223
  · exact B1670227
  · exact B1670231
  · exact B1670235
  · exact B1670239
  · exact B1670243
  · exact B1670247
  · exact B1670251
  · exact B1670255
  · exact B1670259
  · exact B1670263
  · exact B1670267
  · exact B1670271
  · exact B1670275
  · exact B1670279
  · exact B1670283
  · exact B1670287
  · exact B1670291
  · exact B1670295
  · exact B1670299
  · exact B1670303
  · exact B1670307
  · exact B1670311
  · exact B1670315
  · exact B1670319
  · exact B1670323
  · exact B1670327
  · exact B1670331
  · exact B1670335
  · exact B1670339
  · exact B1670343
  · exact B1670347
  · exact B1670351
  · exact B1670355
  · exact B1670359
  · exact B1670363
  · exact B1670367
  · exact B1670371
  · exact B1670375
  · exact B1670379
  · exact B1670383
  · exact B1670387
  · exact B1670391
  · exact B1670395
  · exact B1670399
  · exact B1670403
  · exact B1670407
  · exact B1670411
  · exact B1670415
  · exact B1670419
  · exact B1670423
  · exact B1670427
  · exact B1670431
  · exact B1670435
  · exact B1670439
  · exact B1670443
  · exact B1670447
  · exact B1670451
  · exact B1670455
  · exact B1670459
  · exact B1670463
  · exact B1670467
  · exact B1670471
  · exact B1670475
  · exact B1670479
  · exact B1670483
  · exact B1670487
  · exact B1670491
  · exact B1670495
  · exact B1670499
  · exact B1670503
  · exact B1670507
  · exact B1670511
  · exact B1670515
  · exact B1670519
  · exact B1670523
  · exact B1670527
  · exact B1670531
  · exact B1670535
  · exact B1670539
  · exact B1670543
  · exact B1670547
  · exact B1670551
  · exact B1670555
  · exact B1670559
  · exact B1670563
  · exact B1670567
  · exact B1670571
  · exact B1670575
  · exact B1670579
  · exact B1670583
  · exact B1670587
  · exact B1670591
  · exact B1670595
  · exact B1670599
  · exact B1670603
  · exact B1670607
  · exact B1670611
  · exact B1670615
  · exact B1670619
  · exact B1670623
  · exact B1670627
  · exact B1670631
  · exact B1670635
  · exact B1670639
  · exact B1670643
  · exact B1670647
  · exact B1670651
  · exact B1670655
  · exact B1670659
  · exact B1670663
  · exact B1670667
  · exact B1670671
  · exact B1670675
  · exact B1670679
  · exact B1670683
  · exact B1670687
  · exact B1670691
  · exact B1670695
  · exact B1670699
  · exact B1670703
  · exact B1670707
  · exact B1670711
  · exact B1670715
  · exact B1670719
  · exact B1670723
  · exact B1670727
  · exact B1670731
  · exact B1670735
  · exact B1670739
  · exact B1670743
  · exact B1670747
  · exact B1670751
  · exact B1670755
  · exact B1670759
  · exact B1670763
  · exact B1670767
  · exact B1670771
  · exact B1670775
  · exact B1670779
  · exact B1670783
  · exact B1670787
  · exact B1670791
  · exact B1670795
  · exact B1670799
  · exact B1670803
  · exact B1670807
  · exact B1670811
  · exact B1670815
  · exact B1670819
  · exact B1670823
  · exact B1670827
  · exact B1670831
  · exact B1670835
  · exact B1670839
  · exact B1670843
  · exact B1670847
  · exact B1670851
  · exact B1670855
  · exact B1670859
  · exact B1670863
  · exact B1670867
  · exact B1670871
  · exact B1670875
  · exact B1670879
  · exact B1670883
  · exact B1670887
  · exact B1670891
  · exact B1670895
  · exact B1670899
  · exact B1670903
  · exact B1670907
  · exact B1670911
  · exact B1670915
  · exact B1670919
  · exact B1670923
  · exact B1670927
  · exact B1670931
  · exact B1670935
  · exact B1670939
  · exact B1670943
  · exact B1670947
  · exact B1670951
  · exact B1670955
  · exact B1670959
  · exact B1670963
  · exact B1670967
  · exact B1670971
  · exact B1670975
  · exact B1670979
  · exact B1670983
  · exact B1670987
  · exact B1670991
  · exact B1670995
  · exact B1670999
  · exact B1671003
  · exact B1671007
  · exact B1671011
  · exact B1671015
  · exact B1671019
  · exact B1671023
  · exact B1671027
  · exact B1671031
  · exact B1671035
  · exact B1671039
  · exact B1671043
  · exact B1671047
  · exact B1671051
  · exact B1671055
  · exact B1671059
  · exact B1671063
  · exact B1671067
  · exact B1671071
  · exact B1671075
  · exact B1671079
  · exact B1671083
  · exact B1671087
  · exact B1671091
  · exact B1671095
  · exact B1671099
  · exact B1671103
  · exact B1671107
  · exact B1671111
  · exact B1671115
  · exact B1671119
  · exact B1671123
  · exact B1671127
  · exact B1671131
  · exact B1671135
  · exact B1671139
  · exact B1671143
  · exact B1671147
  · exact B1671151
  · exact B1671155
  · exact B1671159
  · exact B1671163
  · exact B1671167
  · exact B1671171
  · exact B1671175
  · exact B1671179
  · exact B1671183
  · exact B1671187
  · exact B1671191
  · exact B1671195
  · exact B1671199
  · exact B1671203
  · exact B1671207
  · exact B1671211
  · exact B1671215
  · exact B1671219
  · exact B1671223
  · exact B1671227
  · exact B1671231
  · exact B1671235
  · exact B1671239
  · exact B1671243
  · exact B1671247
  · exact B1671251
  · exact B1671255
  · exact B1671259
  · exact B1671263
  · exact B1671267
  · exact B1671271
  · exact B1671275
  · exact B1671279
  · exact B1671283
  · exact B1671287
  · exact B1671291
  · exact B1671295
  · exact B1671299
  · exact B1671303
  · exact B1671307
  · exact B1671311
  · exact B1671315
  · exact B1671319
  · exact B1671323
  · exact B1671327
  · exact B1671331
  · exact B1671335
  · exact B1671339
  · exact B1671343
  · exact B1671347
  · exact B1671351
  · exact B1671355
  · exact B1671359
  · exact B1671363
  · exact B1671367
  · exact B1671371
  · exact B1671375
  · exact B1671379
  · exact B1671383
  · exact B1671387
  · exact B1671391
  · exact B1671395
  · exact B1671399
  · exact B1671403
  · exact B1671407
  · exact B1671411
  · exact B1671415
  · exact B1671419
  · exact B1671423
  · exact B1671427
  · exact B1671431
  · exact B1671435
  · exact B1671439
  · exact B1671443
  · exact B1671447
  · exact B1671451
  · exact B1671455
  · exact B1671459
  · exact B1671463
  · exact B1671467
  · exact B1671471
  · exact B1671475
  · exact B1671479
  · exact B1671483
  · exact B1671487
  · exact B1671491
  · exact B1671495
  · exact B1671499
  · exact B1671503
  · exact B1671507
  · exact B1671511
  · exact B1671515
  · exact B1671519
  · exact B1671523
  · exact B1671527
  · exact B1671531
  · exact B1671535
  · exact B1671539
  · exact B1671543
  · exact B1671547
  · exact B1671551
  · exact B1671555
  · exact B1671559
  · exact B1671563
  · exact B1671567
  · exact B1671571
  · exact B1671575
  · exact B1671579
  · exact B1671583
  · exact B1671587
  · exact B1671591
  · exact B1671595
  · exact B1671599
  · exact B1671603
  · exact B1671607
  · exact B1671611
  · exact B1671615
  · exact B1671619
  · exact B1671623
  · exact B1671627
  · exact B1671631
  · exact B1671635
  · exact B1671639
  · exact B1671643
  · exact B1671647
  · exact B1671651
  · exact B1671655
  · exact B1671659
  · exact B1671663
  · exact B1671667
  · exact B1671671
  · exact B1671675
  · exact B1671679
  · exact B1671683
  · exact B1671687
  · exact B1671691
  · exact B1671695
  · exact B1671699
  · exact B1671703
  · exact B1671707
  · exact B1671711
  · exact B1671715
  · exact B1671719
  · exact B1671723
  · exact B1671727
  · exact B1671731
  · exact B1671735
  · exact B1671739
  · exact B1671743
  · exact B1671747
  · exact B1671751
  · exact B1671755
  · exact B1671759
  · exact B1671763
  · exact B1671767
  · exact B1671771
  · exact B1671775
  · exact B1671779
  · exact B1671783
  · exact B1671787
  · exact B1671791
  · exact B1671795
  · exact B1671799
  · exact B1671803
  · exact B1671807
  · exact B1671811
  · exact B1671815
  · exact B1671819
  · exact B1671823
  · exact B1671827
  · exact B1671831
  · exact B1671835
  · exact B1671839
  · exact B1671843
  · exact B1671847
  · exact B1671851
  · exact B1671855
  · exact B1671859
  · exact B1671863
  · exact B1671867
  · exact B1671871
  · exact B1671875
  · exact B1671879
  · exact B1671883
  · exact B1671887
  · exact B1671891
  · exact B1671895
  · exact B1671899
  · exact B1671903
  · exact B1671907
  · exact B1671911
  · exact B1671915
  · exact B1671919
  · exact B1671923
  · exact B1671927
  · exact B1671931
  · exact B1671935
  · exact B1671939
  · exact B1671943
  · exact B1671947
  · exact B1671951
  · exact B1671955
  · exact B1671959
  · exact B1671963
  · exact B1671967
  · exact B1671971
  · exact B1671975
  · exact B1671979
  · exact B1671983
  · exact B1671987
  · exact B1671991
  · exact B1671995
  · exact B1671999
  · exact B1672003
  · exact B1672007
  · exact B1672011
  · exact B1672015
  · exact B1672019
  · exact B1672023
  · exact B1672027
  · exact B1672031
  · exact B1672035

theorem solution (m : ℕ) (hlo : 1670035 ≤ m) (hhi : m ≤ 1672035) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 417508 ≤ j := by omega
    have hj2 : j ≤ 418008 := by omega
    have hb : Blo 1670035 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
