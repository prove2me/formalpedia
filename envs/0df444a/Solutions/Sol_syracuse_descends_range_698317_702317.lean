-- Prove2me | solution 1 for syracuse_descends_range_698317_702317
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:58.883868+00:00
-- url     : https://prove2.me/submissions/b1cdef55-0496-40e7-8fb4-a4300619aa2e

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


theorem B786433 : Blo 698317 786433 := bbase (se 2 (by rfl) ⟨294912, by rfl⟩ : syracuseStep 786433 = 589825) (by norm_num)
theorem B1769485 : Blo 698317 1769485 := bbase (se 3 (by rfl) ⟨331778, by rfl⟩ : syracuseStep 1769485 = 663557) (by norm_num)
theorem B1048589 : Blo 698317 1048589 := bbase (se 3 (by rfl) ⟨196610, by rfl⟩ : syracuseStep 1048589 = 393221) (by norm_num)
theorem B1572893 : Blo 698317 1572893 := bbase (se 3 (by rfl) ⟨294917, by rfl⟩ : syracuseStep 1572893 = 589835) (by norm_num)
theorem B1179677 : Blo 698317 1179677 := bbase (se 3 (by rfl) ⟨221189, by rfl⟩ : syracuseStep 1179677 = 442379) (by norm_num)
theorem B1048613 : Blo 698317 1048613 := bbase (se 4 (by rfl) ⟨98307, by rfl⟩ : syracuseStep 1048613 = 196615) (by norm_num)
theorem B884773 : Blo 698317 884773 := bbase (se 4 (by rfl) ⟨82947, by rfl⟩ : syracuseStep 884773 = 165895) (by norm_num)
theorem B786469 : Blo 698317 786469 := bbase (se 4 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 786469 = 147463) (by norm_num)
theorem B1048637 : Blo 698317 1048637 := bbase (se 3 (by rfl) ⟨196619, by rfl⟩ : syracuseStep 1048637 = 393239) (by norm_num)
theorem B786505 : Blo 698317 786505 := bbase (se 2 (by rfl) ⟨294939, by rfl⟩ : syracuseStep 786505 = 589879) (by norm_num)
theorem B1048661 : Blo 698317 1048661 := bbase (se 8 (by rfl) ⟨6144, by rfl⟩ : syracuseStep 1048661 = 12289) (by norm_num)
theorem B1572965 : Blo 698317 1572965 := bbase (se 4 (by rfl) ⟨147465, by rfl⟩ : syracuseStep 1572965 = 294931) (by norm_num)
theorem B1048685 : Blo 698317 1048685 := bbase (se 3 (by rfl) ⟨196628, by rfl⟩ : syracuseStep 1048685 = 393257) (by norm_num)
theorem B786541 : Blo 698317 786541 := bbase (se 3 (by rfl) ⟨147476, by rfl⟩ : syracuseStep 786541 = 294953) (by norm_num)
theorem B1441901 : Blo 698317 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B1769597 : Blo 698317 1769597 := bbase (se 3 (by rfl) ⟨331799, by rfl⟩ : syracuseStep 1769597 = 663599) (by norm_num)
theorem B1048709 : Blo 698317 1048709 := bbase (se 4 (by rfl) ⟨98316, by rfl⟩ : syracuseStep 1048709 = 196633) (by norm_num)
theorem B786577 : Blo 698317 786577 := bbase (se 2 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 786577 = 589933) (by norm_num)
theorem B1179805 : Blo 698317 1179805 := bbase (se 3 (by rfl) ⟨221213, by rfl⟩ : syracuseStep 1179805 = 442427) (by norm_num)
theorem B1048733 : Blo 698317 1048733 := bbase (se 3 (by rfl) ⟨196637, by rfl⟩ : syracuseStep 1048733 = 393275) (by norm_num)
theorem B1573037 : Blo 698317 1573037 := bbase (se 3 (by rfl) ⟨294944, by rfl⟩ : syracuseStep 1573037 = 589889) (by norm_num)
theorem B1048757 : Blo 698317 1048757 := bbase (se 5 (by rfl) ⟨49160, by rfl⟩ : syracuseStep 1048757 = 98321) (by norm_num)
theorem B786613 : Blo 698317 786613 := bbase (se 5 (by rfl) ⟨36872, by rfl⟩ : syracuseStep 786613 = 73745) (by norm_num)
theorem B1048781 : Blo 698317 1048781 := bbase (se 3 (by rfl) ⟨196646, by rfl⟩ : syracuseStep 1048781 = 393293) (by norm_num)
theorem B884945 : Blo 698317 884945 := bbase (se 2 (by rfl) ⟨331854, by rfl⟩ : syracuseStep 884945 = 663709) (by norm_num)
theorem B786649 : Blo 698317 786649 := bbase (se 2 (by rfl) ⟨294993, by rfl⟩ : syracuseStep 786649 = 589987) (by norm_num)
theorem B1048805 : Blo 698317 1048805 := bbase (se 4 (by rfl) ⟨98325, by rfl⟩ : syracuseStep 1048805 = 196651) (by norm_num)
theorem B1573109 : Blo 698317 1573109 := bbase (se 5 (by rfl) ⟨73739, by rfl⟩ : syracuseStep 1573109 = 147479) (by norm_num)
theorem B1179893 : Blo 698317 1179893 := bbase (se 5 (by rfl) ⟨55307, by rfl⟩ : syracuseStep 1179893 = 110615) (by norm_num)
theorem B1048829 : Blo 698317 1048829 := bbase (se 3 (by rfl) ⟨196655, by rfl⟩ : syracuseStep 1048829 = 393311) (by norm_num)
theorem B786685 : Blo 698317 786685 := bbase (se 3 (by rfl) ⟨147503, by rfl⟩ : syracuseStep 786685 = 295007) (by norm_num)
theorem B885001 : Blo 698317 885001 := bbase (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) (by norm_num)
theorem B1048853 : Blo 698317 1048853 := bbase (se 6 (by rfl) ⟨24582, by rfl⟩ : syracuseStep 1048853 = 49165) (by norm_num)
theorem B786721 : Blo 698317 786721 := bbase (se 2 (by rfl) ⟨295020, by rfl⟩ : syracuseStep 786721 = 590041) (by norm_num)
theorem B1048877 : Blo 698317 1048877 := bbase (se 3 (by rfl) ⟨196664, by rfl⟩ : syracuseStep 1048877 = 393329) (by norm_num)
theorem B1769789 : Blo 698317 1769789 := bbase (se 3 (by rfl) ⟨331835, by rfl⟩ : syracuseStep 1769789 = 663671) (by norm_num)
theorem B1573181 : Blo 698317 1573181 := bbase (se 3 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 1573181 = 589943) (by norm_num)
theorem B1048901 : Blo 698317 1048901 := bbase (se 4 (by rfl) ⟨98334, by rfl⟩ : syracuseStep 1048901 = 196669) (by norm_num)
theorem B786757 : Blo 698317 786757 := bbase (se 4 (by rfl) ⟨73758, by rfl⟩ : syracuseStep 786757 = 147517) (by norm_num)
theorem B2359637 : Blo 698317 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B1048925 : Blo 698317 1048925 := bbase (se 3 (by rfl) ⟨196673, by rfl⟩ : syracuseStep 1048925 = 393347) (by norm_num)
theorem B885097 : Blo 698317 885097 := bbase (se 2 (by rfl) ⟨331911, by rfl⟩ : syracuseStep 885097 = 663823) (by norm_num)
theorem B786793 : Blo 698317 786793 := bbase (se 2 (by rfl) ⟨295047, by rfl⟩ : syracuseStep 786793 = 590095) (by norm_num)
theorem B1180021 : Blo 698317 1180021 := bbase (se 5 (by rfl) ⟨55313, by rfl⟩ : syracuseStep 1180021 = 110627) (by norm_num)
theorem B1048949 : Blo 698317 1048949 := bbase (se 5 (by rfl) ⟨49169, by rfl⟩ : syracuseStep 1048949 = 98339) (by norm_num)
theorem B1573253 : Blo 698317 1573253 := bbase (se 4 (by rfl) ⟨147492, by rfl⟩ : syracuseStep 1573253 = 294985) (by norm_num)
theorem B1999237 : Blo 698317 1999237 := bbase (se 4 (by rfl) ⟨187428, by rfl⟩ : syracuseStep 1999237 = 374857) (by norm_num)
theorem B1048973 : Blo 698317 1048973 := bbase (se 3 (by rfl) ⟨196682, by rfl⟩ : syracuseStep 1048973 = 393365) (by norm_num)
theorem B786829 : Blo 698317 786829 := bbase (se 3 (by rfl) ⟨147530, by rfl⟩ : syracuseStep 786829 = 295061) (by norm_num)
theorem B1048997 : Blo 698317 1048997 := bbase (se 4 (by rfl) ⟨98343, by rfl⟩ : syracuseStep 1048997 = 196687) (by norm_num)
theorem B786865 : Blo 698317 786865 := bbase (se 2 (by rfl) ⟨295074, by rfl⟩ : syracuseStep 786865 = 590149) (by norm_num)
theorem B1049021 : Blo 698317 1049021 := bbase (se 3 (by rfl) ⟨196691, by rfl⟩ : syracuseStep 1049021 = 393383) (by norm_num)
theorem B1573325 : Blo 698317 1573325 := bbase (se 3 (by rfl) ⟨294998, by rfl⟩ : syracuseStep 1573325 = 589997) (by norm_num)
theorem B1180109 : Blo 698317 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B1049045 : Blo 698317 1049045 := bbase (se 7 (by rfl) ⟨12293, by rfl⟩ : syracuseStep 1049045 = 24587) (by norm_num)
theorem B786901 : Blo 698317 786901 := bbase (se 7 (by rfl) ⟨9221, by rfl⟩ : syracuseStep 786901 = 18443) (by norm_num)
theorem B1049069 : Blo 698317 1049069 := bbase (se 3 (by rfl) ⟨196700, by rfl⟩ : syracuseStep 1049069 = 393401) (by norm_num)
theorem B786937 : Blo 698317 786937 := bbase (se 2 (by rfl) ⟨295101, by rfl⟩ : syracuseStep 786937 = 590203) (by norm_num)
theorem B1049093 : Blo 698317 1049093 := bbase (se 4 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 1049093 = 196705) (by norm_num)
theorem B1573397 : Blo 698317 1573397 := bbase (se 6 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 1573397 = 73753) (by norm_num)
theorem B885269 : Blo 698317 885269 := bbase (se 6 (by rfl) ⟨20748, by rfl⟩ : syracuseStep 885269 = 41497) (by norm_num)
theorem B1049117 : Blo 698317 1049117 := bbase (se 3 (by rfl) ⟨196709, by rfl⟩ : syracuseStep 1049117 = 393419) (by norm_num)
theorem B786973 : Blo 698317 786973 := bbase (se 3 (by rfl) ⟨147557, by rfl⟩ : syracuseStep 786973 = 295115) (by norm_num)
theorem B1999397 : Blo 698317 1999397 := bbase (se 4 (by rfl) ⟨187443, by rfl⟩ : syracuseStep 1999397 = 374887) (by norm_num)
theorem B1049141 : Blo 698317 1049141 := bbase (se 5 (by rfl) ⟨49178, by rfl⟩ : syracuseStep 1049141 = 98357) (by norm_num)
theorem B787009 : Blo 698317 787009 := bbase (se 2 (by rfl) ⟨295128, by rfl⟩ : syracuseStep 787009 = 590257) (by norm_num)
theorem B1180237 : Blo 698317 1180237 := bbase (se 3 (by rfl) ⟨221294, by rfl⟩ : syracuseStep 1180237 = 442589) (by norm_num)
theorem B1049165 : Blo 698317 1049165 := bbase (se 3 (by rfl) ⟨196718, by rfl⟩ : syracuseStep 1049165 = 393437) (by norm_num)
theorem B885325 : Blo 698317 885325 := bbase (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) (by norm_num)
theorem B1573469 : Blo 698317 1573469 := bbase (se 3 (by rfl) ⟨295025, by rfl⟩ : syracuseStep 1573469 = 590051) (by norm_num)
theorem B1049189 : Blo 698317 1049189 := bbase (se 4 (by rfl) ⟨98361, by rfl⟩ : syracuseStep 1049189 = 196723) (by norm_num)
theorem B787045 : Blo 698317 787045 := bbase (se 4 (by rfl) ⟨73785, by rfl⟩ : syracuseStep 787045 = 147571) (by norm_num)
theorem B1049213 : Blo 698317 1049213 := bbase (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) (by norm_num)
theorem B787081 : Blo 698317 787081 := bbase (se 2 (by rfl) ⟨295155, by rfl⟩ : syracuseStep 787081 = 590311) (by norm_num)
theorem B1770133 : Blo 698317 1770133 := bbase (se 6 (by rfl) ⟨41487, by rfl⟩ : syracuseStep 1770133 = 82975) (by norm_num)
theorem B1049237 : Blo 698317 1049237 := bbase (se 6 (by rfl) ⟨24591, by rfl⟩ : syracuseStep 1049237 = 49183) (by norm_num)
theorem B1573541 : Blo 698317 1573541 := bbase (se 4 (by rfl) ⟨147519, by rfl⟩ : syracuseStep 1573541 = 295039) (by norm_num)
theorem B1180325 : Blo 698317 1180325 := bbase (se 4 (by rfl) ⟨110655, by rfl⟩ : syracuseStep 1180325 = 221311) (by norm_num)
theorem B1049261 : Blo 698317 1049261 := bbase (se 3 (by rfl) ⟨196736, by rfl⟩ : syracuseStep 1049261 = 393473) (by norm_num)
theorem B885421 : Blo 698317 885421 := bbase (se 3 (by rfl) ⟨166016, by rfl⟩ : syracuseStep 885421 = 332033) (by norm_num)
theorem B787117 : Blo 698317 787117 := bbase (se 3 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 787117 = 295169) (by norm_num)
theorem B1049285 : Blo 698317 1049285 := bbase (se 4 (by rfl) ⟨98370, by rfl⟩ : syracuseStep 1049285 = 196741) (by norm_num)
theorem B1344205 : Blo 698317 1344205 := bbase (se 3 (by rfl) ⟨252038, by rfl⟩ : syracuseStep 1344205 = 504077) (by norm_num)
theorem B787153 : Blo 698317 787153 := bbase (se 2 (by rfl) ⟨295182, by rfl⟩ : syracuseStep 787153 = 590365) (by norm_num)
theorem B1049309 : Blo 698317 1049309 := bbase (se 3 (by rfl) ⟨196745, by rfl⟩ : syracuseStep 1049309 = 393491) (by norm_num)
theorem B1573613 : Blo 698317 1573613 := bbase (se 3 (by rfl) ⟨295052, by rfl⟩ : syracuseStep 1573613 = 590105) (by norm_num)
theorem B1049333 : Blo 698317 1049333 := bbase (se 5 (by rfl) ⟨49187, by rfl⟩ : syracuseStep 1049333 = 98375) (by norm_num)
theorem B787189 : Blo 698317 787189 := bbase (se 5 (by rfl) ⟨36899, by rfl⟩ : syracuseStep 787189 = 73799) (by norm_num)
theorem B2360069 : Blo 698317 2360069 := bbase (se 4 (by rfl) ⟨221256, by rfl⟩ : syracuseStep 2360069 = 442513) (by norm_num)
theorem B1770245 : Blo 698317 1770245 := bbase (se 4 (by rfl) ⟨165960, by rfl⟩ : syracuseStep 1770245 = 331921) (by norm_num)
theorem B1049357 : Blo 698317 1049357 := bbase (se 3 (by rfl) ⟨196754, by rfl⟩ : syracuseStep 1049357 = 393509) (by norm_num)
theorem B1999637 : Blo 698317 1999637 := bbase (se 6 (by rfl) ⟨46866, by rfl⟩ : syracuseStep 1999637 = 93733) (by norm_num)
theorem B787225 : Blo 698317 787225 := bbase (se 2 (by rfl) ⟨295209, by rfl⟩ : syracuseStep 787225 = 590419) (by norm_num)
theorem B1180453 : Blo 698317 1180453 := bbase (se 4 (by rfl) ⟨110667, by rfl⟩ : syracuseStep 1180453 = 221335) (by norm_num)
theorem B1049381 : Blo 698317 1049381 := bbase (se 4 (by rfl) ⟨98379, by rfl⟩ : syracuseStep 1049381 = 196759) (by norm_num)
theorem B1573685 : Blo 698317 1573685 := bbase (se 5 (by rfl) ⟨73766, by rfl⟩ : syracuseStep 1573685 = 147533) (by norm_num)
theorem B1049405 : Blo 698317 1049405 := bbase (se 3 (by rfl) ⟨196763, by rfl⟩ : syracuseStep 1049405 = 393527) (by norm_num)
theorem B787261 : Blo 698317 787261 := bbase (se 3 (by rfl) ⟨147611, by rfl⟩ : syracuseStep 787261 = 295223) (by norm_num)
theorem B1049429 : Blo 698317 1049429 := bbase (se 9 (by rfl) ⟨3074, by rfl⟩ : syracuseStep 1049429 = 6149) (by norm_num)
theorem B885593 : Blo 698317 885593 := bbase (se 2 (by rfl) ⟨332097, by rfl⟩ : syracuseStep 885593 = 664195) (by norm_num)
theorem B787297 : Blo 698317 787297 := bbase (se 2 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 787297 = 590473) (by norm_num)
theorem B1049453 : Blo 698317 1049453 := bbase (se 3 (by rfl) ⟨196772, by rfl⟩ : syracuseStep 1049453 = 393545) (by norm_num)
theorem B1573757 : Blo 698317 1573757 := bbase (se 3 (by rfl) ⟨295079, by rfl⟩ : syracuseStep 1573757 = 590159) (by norm_num)
theorem B1180541 : Blo 698317 1180541 := bbase (se 3 (by rfl) ⟨221351, by rfl⟩ : syracuseStep 1180541 = 442703) (by norm_num)
theorem B1049477 : Blo 698317 1049477 := bbase (se 4 (by rfl) ⟨98388, by rfl⟩ : syracuseStep 1049477 = 196777) (by norm_num)
theorem B787333 : Blo 698317 787333 := bbase (se 4 (by rfl) ⟨73812, by rfl⟩ : syracuseStep 787333 = 147625) (by norm_num)
theorem B885649 : Blo 698317 885649 := bbase (se 2 (by rfl) ⟨332118, by rfl⟩ : syracuseStep 885649 = 664237) (by norm_num)
theorem B3539861 : Blo 698317 3539861 := bbase (se 6 (by rfl) ⟨82965, by rfl⟩ : syracuseStep 3539861 = 165931) (by norm_num)
theorem B2655125 : Blo 698317 2655125 := bbase (se 6 (by rfl) ⟨62229, by rfl⟩ : syracuseStep 2655125 = 124459) (by norm_num)
theorem B1049501 : Blo 698317 1049501 := bbase (se 3 (by rfl) ⟨196781, by rfl⟩ : syracuseStep 1049501 = 393563) (by norm_num)
theorem B787369 : Blo 698317 787369 := bbase (se 2 (by rfl) ⟨295263, by rfl⟩ : syracuseStep 787369 = 590527) (by norm_num)
theorem B1049525 : Blo 698317 1049525 := bbase (se 5 (by rfl) ⟨49196, by rfl⟩ : syracuseStep 1049525 = 98393) (by norm_num)
theorem B1770437 : Blo 698317 1770437 := bbase (se 4 (by rfl) ⟨165978, by rfl⟩ : syracuseStep 1770437 = 331957) (by norm_num)
theorem B1573829 : Blo 698317 1573829 := bbase (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) (by norm_num)
theorem B1049549 : Blo 698317 1049549 := bbase (se 3 (by rfl) ⟨196790, by rfl⟩ : syracuseStep 1049549 = 393581) (by norm_num)
theorem B787405 : Blo 698317 787405 := bbase (se 3 (by rfl) ⟨147638, by rfl⟩ : syracuseStep 787405 = 295277) (by norm_num)
theorem B1999829 : Blo 698317 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B1049573 : Blo 698317 1049573 := bbase (se 4 (by rfl) ⟨98397, by rfl⟩ : syracuseStep 1049573 = 196795) (by norm_num)
theorem B885745 : Blo 698317 885745 := bbase (se 2 (by rfl) ⟨332154, by rfl⟩ : syracuseStep 885745 = 664309) (by norm_num)
theorem B787441 : Blo 698317 787441 := bbase (se 2 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 787441 = 590581) (by norm_num)
theorem B2556917 : Blo 698317 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B1180669 : Blo 698317 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B1049597 : Blo 698317 1049597 := bbase (se 3 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 1049597 = 393599) (by norm_num)
theorem B1573901 : Blo 698317 1573901 := bbase (se 3 (by rfl) ⟨295106, by rfl⟩ : syracuseStep 1573901 = 590213) (by norm_num)
theorem B1049621 : Blo 698317 1049621 := bbase (se 6 (by rfl) ⟨24600, by rfl⟩ : syracuseStep 1049621 = 49201) (by norm_num)
theorem B787477 : Blo 698317 787477 := bbase (se 6 (by rfl) ⟨18456, by rfl⟩ : syracuseStep 787477 = 36913) (by norm_num)
theorem B1049645 : Blo 698317 1049645 := bbase (se 3 (by rfl) ⟨196808, by rfl⟩ : syracuseStep 1049645 = 393617) (by norm_num)
theorem B787513 : Blo 698317 787513 := bbase (se 2 (by rfl) ⟨295317, by rfl⟩ : syracuseStep 787513 = 590635) (by norm_num)
theorem B1049669 : Blo 698317 1049669 := bbase (se 4 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 1049669 = 196813) (by norm_num)
theorem B1573973 : Blo 698317 1573973 := bbase (se 8 (by rfl) ⟨9222, by rfl⟩ : syracuseStep 1573973 = 18445) (by norm_num)
theorem B1180757 : Blo 698317 1180757 := bbase (se 8 (by rfl) ⟨6918, by rfl⟩ : syracuseStep 1180757 = 13837) (by norm_num)
theorem B1049693 : Blo 698317 1049693 := bbase (se 3 (by rfl) ⟨196817, by rfl⟩ : syracuseStep 1049693 = 393635) (by norm_num)
theorem B787549 : Blo 698317 787549 := bbase (se 3 (by rfl) ⟨147665, by rfl⟩ : syracuseStep 787549 = 295331) (by norm_num)
theorem B1049717 : Blo 698317 1049717 := bbase (se 5 (by rfl) ⟨49205, by rfl⟩ : syracuseStep 1049717 = 98411) (by norm_num)
theorem B787585 : Blo 698317 787585 := bbase (se 2 (by rfl) ⟨295344, by rfl⟩ : syracuseStep 787585 = 590689) (by norm_num)
theorem B1049741 : Blo 698317 1049741 := bbase (se 3 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 1049741 = 393653) (by norm_num)
theorem B1574045 : Blo 698317 1574045 := bbase (se 3 (by rfl) ⟨295133, by rfl⟩ : syracuseStep 1574045 = 590267) (by norm_num)
theorem B885917 : Blo 698317 885917 := bbase (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) (by norm_num)
theorem B1049765 : Blo 698317 1049765 := bbase (se 4 (by rfl) ⟨98415, by rfl⟩ : syracuseStep 1049765 = 196831) (by norm_num)
theorem B787621 : Blo 698317 787621 := bbase (se 4 (by rfl) ⟨73839, by rfl⟩ : syracuseStep 787621 = 147679) (by norm_num)
theorem B2655413 : Blo 698317 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B2360501 : Blo 698317 2360501 := bbase (se 5 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 2360501 = 221297) (by norm_num)
theorem B1049789 : Blo 698317 1049789 := bbase (se 3 (by rfl) ⟨196835, by rfl⟩ : syracuseStep 1049789 = 393671) (by norm_num)
theorem B787657 : Blo 698317 787657 := bbase (se 2 (by rfl) ⟨295371, by rfl⟩ : syracuseStep 787657 = 590743) (by norm_num)
theorem B1180885 : Blo 698317 1180885 := bbase (se 7 (by rfl) ⟨13838, by rfl⟩ : syracuseStep 1180885 = 27677) (by norm_num)
theorem B1049813 : Blo 698317 1049813 := bbase (se 7 (by rfl) ⟨12302, by rfl⟩ : syracuseStep 1049813 = 24605) (by norm_num)
theorem B885973 : Blo 698317 885973 := bbase (se 7 (by rfl) ⟨10382, by rfl⟩ : syracuseStep 885973 = 20765) (by norm_num)
theorem B1574117 : Blo 698317 1574117 := bbase (se 4 (by rfl) ⟨147573, by rfl⟩ : syracuseStep 1574117 = 295147) (by norm_num)
theorem B1049837 : Blo 698317 1049837 := bbase (se 3 (by rfl) ⟨196844, by rfl⟩ : syracuseStep 1049837 = 393689) (by norm_num)
theorem B787693 : Blo 698317 787693 := bbase (se 3 (by rfl) ⟨147692, by rfl⟩ : syracuseStep 787693 = 295385) (by norm_num)
theorem B1049861 : Blo 698317 1049861 := bbase (se 4 (by rfl) ⟨98424, by rfl⟩ : syracuseStep 1049861 = 196849) (by norm_num)
theorem B787729 : Blo 698317 787729 := bbase (se 2 (by rfl) ⟨295398, by rfl⟩ : syracuseStep 787729 = 590797) (by norm_num)
theorem B2983189 : Blo 698317 2983189 := bbase (se 6 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 2983189 = 139837) (by norm_num)
theorem B1770781 : Blo 698317 1770781 := bbase (se 3 (by rfl) ⟨332021, by rfl⟩ : syracuseStep 1770781 = 664043) (by norm_num)
theorem B1049885 : Blo 698317 1049885 := bbase (se 3 (by rfl) ⟨196853, by rfl⟩ : syracuseStep 1049885 = 393707) (by norm_num)
theorem B2983205 : Blo 698317 2983205 := bbase (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) (by norm_num)
theorem B1574189 : Blo 698317 1574189 := bbase (se 3 (by rfl) ⟨295160, by rfl⟩ : syracuseStep 1574189 = 590321) (by norm_num)
theorem B1180973 : Blo 698317 1180973 := bbase (se 3 (by rfl) ⟨221432, by rfl⟩ : syracuseStep 1180973 = 442865) (by norm_num)
theorem B1049909 : Blo 698317 1049909 := bbase (se 5 (by rfl) ⟨49214, by rfl⟩ : syracuseStep 1049909 = 98429) (by norm_num)
theorem B886069 : Blo 698317 886069 := bbase (se 5 (by rfl) ⟨41534, by rfl⟩ : syracuseStep 886069 = 83069) (by norm_num)
theorem B787765 : Blo 698317 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B1049933 : Blo 698317 1049933 := bbase (se 3 (by rfl) ⟨196862, by rfl⟩ : syracuseStep 1049933 = 393725) (by norm_num)
theorem B787801 : Blo 698317 787801 := bbase (se 2 (by rfl) ⟨295425, by rfl⟩ : syracuseStep 787801 = 590851) (by norm_num)
theorem B1049957 : Blo 698317 1049957 := bbase (se 4 (by rfl) ⟨98433, by rfl⟩ : syracuseStep 1049957 = 196867) (by norm_num)
theorem B1574261 : Blo 698317 1574261 := bbase (se 5 (by rfl) ⟨73793, by rfl⟩ : syracuseStep 1574261 = 147587) (by norm_num)
theorem B1049981 : Blo 698317 1049981 := bbase (se 3 (by rfl) ⟨196871, by rfl⟩ : syracuseStep 1049981 = 393743) (by norm_num)
theorem B787837 : Blo 698317 787837 := bbase (se 3 (by rfl) ⟨147719, by rfl⟩ : syracuseStep 787837 = 295439) (by norm_num)
theorem B1770893 : Blo 698317 1770893 := bbase (se 3 (by rfl) ⟨332042, by rfl⟩ : syracuseStep 1770893 = 664085) (by norm_num)
theorem B1050005 : Blo 698317 1050005 := bbase (se 6 (by rfl) ⟨24609, by rfl⟩ : syracuseStep 1050005 = 49219) (by norm_num)
theorem B787873 : Blo 698317 787873 := bbase (se 2 (by rfl) ⟨295452, by rfl⟩ : syracuseStep 787873 = 590905) (by norm_num)
theorem B1181101 : Blo 698317 1181101 := bbase (se 3 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 1181101 = 442913) (by norm_num)
theorem B1050029 : Blo 698317 1050029 := bbase (se 3 (by rfl) ⟨196880, by rfl⟩ : syracuseStep 1050029 = 393761) (by norm_num)
theorem B1574333 : Blo 698317 1574333 := bbase (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) (by norm_num)
theorem B1050053 : Blo 698317 1050053 := bbase (se 4 (by rfl) ⟨98442, by rfl⟩ : syracuseStep 1050053 = 196885) (by norm_num)
theorem B787909 : Blo 698317 787909 := bbase (se 4 (by rfl) ⟨73866, by rfl⟩ : syracuseStep 787909 = 147733) (by norm_num)
theorem B1050077 : Blo 698317 1050077 := bbase (se 3 (by rfl) ⟨196889, by rfl⟩ : syracuseStep 1050077 = 393779) (by norm_num)
theorem B886241 : Blo 698317 886241 := bbase (se 2 (by rfl) ⟨332340, by rfl⟩ : syracuseStep 886241 = 664681) (by norm_num)
theorem B787945 : Blo 698317 787945 := bbase (se 2 (by rfl) ⟨295479, by rfl⟩ : syracuseStep 787945 = 590959) (by norm_num)
theorem B1050101 : Blo 698317 1050101 := bbase (se 5 (by rfl) ⟨49223, by rfl⟩ : syracuseStep 1050101 = 98447) (by norm_num)
theorem B1574405 : Blo 698317 1574405 := bbase (se 4 (by rfl) ⟨147600, by rfl⟩ : syracuseStep 1574405 = 295201) (by norm_num)
theorem B1181189 : Blo 698317 1181189 := bbase (se 4 (by rfl) ⟨110736, by rfl⟩ : syracuseStep 1181189 = 221473) (by norm_num)
theorem B1050125 : Blo 698317 1050125 := bbase (se 3 (by rfl) ⟨196898, by rfl⟩ : syracuseStep 1050125 = 393797) (by norm_num)
theorem B787981 : Blo 698317 787981 := bbase (se 3 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 787981 = 295493) (by norm_num)
theorem B886297 : Blo 698317 886297 := bbase (se 2 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 886297 = 664723) (by norm_num)
theorem B1050149 : Blo 698317 1050149 := bbase (se 4 (by rfl) ⟨98451, by rfl⟩ : syracuseStep 1050149 = 196903) (by norm_num)
theorem B788017 : Blo 698317 788017 := bbase (se 2 (by rfl) ⟨295506, by rfl⟩ : syracuseStep 788017 = 591013) (by norm_num)
theorem B1050173 : Blo 698317 1050173 := bbase (se 3 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 1050173 = 393815) (by norm_num)
theorem B1771085 : Blo 698317 1771085 := bbase (se 3 (by rfl) ⟨332078, by rfl⟩ : syracuseStep 1771085 = 664157) (by norm_num)
theorem B1574477 : Blo 698317 1574477 := bbase (se 3 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 1574477 = 590429) (by norm_num)
theorem B23004757 : Blo 698317 23004757 := bbase (se 8 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 23004757 = 269587) (by norm_num)
theorem B1050197 : Blo 698317 1050197 := bbase (se 8 (by rfl) ⟨6153, by rfl⟩ : syracuseStep 1050197 = 12307) (by norm_num)
theorem B788053 : Blo 698317 788053 := bbase (se 8 (by rfl) ⟨4617, by rfl⟩ : syracuseStep 788053 = 9235) (by norm_num)
theorem B2360933 : Blo 698317 2360933 := bbase (se 4 (by rfl) ⟨221337, by rfl⟩ : syracuseStep 2360933 = 442675) (by norm_num)
theorem B1050221 : Blo 698317 1050221 := bbase (se 3 (by rfl) ⟨196916, by rfl⟩ : syracuseStep 1050221 = 393833) (by norm_num)
theorem B886393 : Blo 698317 886393 := bbase (se 2 (by rfl) ⟨332397, by rfl⟩ : syracuseStep 886393 = 664795) (by norm_num)
theorem B788089 : Blo 698317 788089 := bbase (se 2 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 788089 = 591067) (by norm_num)
theorem B1181317 : Blo 698317 1181317 := bbase (se 4 (by rfl) ⟨110748, by rfl⟩ : syracuseStep 1181317 = 221497) (by norm_num)
theorem B1050245 : Blo 698317 1050245 := bbase (se 4 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 1050245 = 196921) (by norm_num)
theorem B2393749 : Blo 698317 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B1574549 : Blo 698317 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B1050269 : Blo 698317 1050269 := bbase (se 3 (by rfl) ⟨196925, by rfl⟩ : syracuseStep 1050269 = 393851) (by norm_num)
theorem B788125 : Blo 698317 788125 := bbase (se 3 (by rfl) ⟨147773, by rfl⟩ : syracuseStep 788125 = 295547) (by norm_num)
theorem B1050293 : Blo 698317 1050293 := bbase (se 5 (by rfl) ⟨49232, by rfl⟩ : syracuseStep 1050293 = 98465) (by norm_num)
theorem B788161 : Blo 698317 788161 := bbase (se 2 (by rfl) ⟨295560, by rfl⟩ : syracuseStep 788161 = 591121) (by norm_num)
theorem B1050317 : Blo 698317 1050317 := bbase (se 3 (by rfl) ⟨196934, by rfl⟩ : syracuseStep 1050317 = 393869) (by norm_num)
theorem B1574621 : Blo 698317 1574621 := bbase (se 3 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 1574621 = 590483) (by norm_num)
theorem B1181405 : Blo 698317 1181405 := bbase (se 3 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 1181405 = 443027) (by norm_num)
theorem B2623205 : Blo 698317 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B1050341 : Blo 698317 1050341 := bbase (se 4 (by rfl) ⟨98469, by rfl⟩ : syracuseStep 1050341 = 196939) (by norm_num)
theorem B788197 : Blo 698317 788197 := bbase (se 4 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 788197 = 147787) (by norm_num)
theorem B1050365 : Blo 698317 1050365 := bbase (se 3 (by rfl) ⟨196943, by rfl⟩ : syracuseStep 1050365 = 393887) (by norm_num)
theorem B788233 : Blo 698317 788233 := bbase (se 2 (by rfl) ⟨295587, by rfl⟩ : syracuseStep 788233 = 591175) (by norm_num)
theorem B1050389 : Blo 698317 1050389 := bbase (se 6 (by rfl) ⟨24618, by rfl⟩ : syracuseStep 1050389 = 49237) (by norm_num)
theorem B1574693 : Blo 698317 1574693 := bbase (se 4 (by rfl) ⟨147627, by rfl⟩ : syracuseStep 1574693 = 295255) (by norm_num)
theorem B886565 : Blo 698317 886565 := bbase (se 4 (by rfl) ⟨83115, by rfl⟩ : syracuseStep 886565 = 166231) (by norm_num)
theorem B1050413 : Blo 698317 1050413 := bbase (se 3 (by rfl) ⟨196952, by rfl⟩ : syracuseStep 1050413 = 393905) (by norm_num)
theorem B788269 : Blo 698317 788269 := bbase (se 3 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 788269 = 295601) (by norm_num)
theorem B1050437 : Blo 698317 1050437 := bbase (se 4 (by rfl) ⟨98478, by rfl⟩ : syracuseStep 1050437 = 196957) (by norm_num)
theorem B788305 : Blo 698317 788305 := bbase (se 2 (by rfl) ⟨295614, by rfl⟩ : syracuseStep 788305 = 591229) (by norm_num)
theorem B1181533 : Blo 698317 1181533 := bbase (se 3 (by rfl) ⟨221537, by rfl⟩ : syracuseStep 1181533 = 443075) (by norm_num)
theorem B1050461 : Blo 698317 1050461 := bbase (se 3 (by rfl) ⟨196961, by rfl⟩ : syracuseStep 1050461 = 393923) (by norm_num)
theorem B886621 : Blo 698317 886621 := bbase (se 3 (by rfl) ⟨166241, by rfl⟩ : syracuseStep 886621 = 332483) (by norm_num)
theorem B1574765 : Blo 698317 1574765 := bbase (se 3 (by rfl) ⟨295268, by rfl⟩ : syracuseStep 1574765 = 590537) (by norm_num)
theorem B1050485 : Blo 698317 1050485 := bbase (se 5 (by rfl) ⟨49241, by rfl⟩ : syracuseStep 1050485 = 98483) (by norm_num)
theorem B788341 : Blo 698317 788341 := bbase (se 5 (by rfl) ⟨36953, by rfl⟩ : syracuseStep 788341 = 73907) (by norm_num)
theorem B1050509 : Blo 698317 1050509 := bbase (se 3 (by rfl) ⟨196970, by rfl⟩ : syracuseStep 1050509 = 393941) (by norm_num)
theorem B788377 : Blo 698317 788377 := bbase (se 2 (by rfl) ⟨295641, by rfl⟩ : syracuseStep 788377 = 591283) (by norm_num)
theorem B1771429 : Blo 698317 1771429 := bbase (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) (by norm_num)
theorem B1050533 : Blo 698317 1050533 := bbase (se 4 (by rfl) ⟨98487, by rfl⟩ : syracuseStep 1050533 = 196975) (by norm_num)
theorem B1574837 : Blo 698317 1574837 := bbase (se 5 (by rfl) ⟨73820, by rfl⟩ : syracuseStep 1574837 = 147641) (by norm_num)
theorem B1181621 : Blo 698317 1181621 := bbase (se 5 (by rfl) ⟨55388, by rfl⟩ : syracuseStep 1181621 = 110777) (by norm_num)
theorem B1050557 : Blo 698317 1050557 := bbase (se 3 (by rfl) ⟨196979, by rfl⟩ : syracuseStep 1050557 = 393959) (by norm_num)
theorem B886717 : Blo 698317 886717 := bbase (se 3 (by rfl) ⟨166259, by rfl⟩ : syracuseStep 886717 = 332519) (by norm_num)
theorem B788413 : Blo 698317 788413 := bbase (se 3 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 788413 = 295655) (by norm_num)
theorem B1050581 : Blo 698317 1050581 := bbase (se 7 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 1050581 = 24623) (by norm_num)
theorem B788449 : Blo 698317 788449 := bbase (se 2 (by rfl) ⟨295668, by rfl⟩ : syracuseStep 788449 = 591337) (by norm_num)
theorem B1050605 : Blo 698317 1050605 := bbase (se 3 (by rfl) ⟨196988, by rfl⟩ : syracuseStep 1050605 = 393977) (by norm_num)
theorem B1574909 : Blo 698317 1574909 := bbase (se 3 (by rfl) ⟨295295, by rfl⟩ : syracuseStep 1574909 = 590591) (by norm_num)
theorem B1050629 : Blo 698317 1050629 := bbase (se 4 (by rfl) ⟨98496, by rfl⟩ : syracuseStep 1050629 = 196993) (by norm_num)
theorem B788485 : Blo 698317 788485 := bbase (se 4 (by rfl) ⟨73920, by rfl⟩ : syracuseStep 788485 = 147841) (by norm_num)
theorem B2361365 : Blo 698317 2361365 := bbase (se 6 (by rfl) ⟨55344, by rfl⟩ : syracuseStep 2361365 = 110689) (by norm_num)
theorem B1771541 : Blo 698317 1771541 := bbase (se 6 (by rfl) ⟨41520, by rfl⟩ : syracuseStep 1771541 = 83041) (by norm_num)
theorem B1050653 : Blo 698317 1050653 := bbase (se 3 (by rfl) ⟨196997, by rfl⟩ : syracuseStep 1050653 = 393995) (by norm_num)
theorem B788521 : Blo 698317 788521 := bbase (se 2 (by rfl) ⟨295695, by rfl⟩ : syracuseStep 788521 = 591391) (by norm_num)
theorem B1181749 : Blo 698317 1181749 := bbase (se 5 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 1181749 = 110789) (by norm_num)
theorem B1050677 : Blo 698317 1050677 := bbase (se 5 (by rfl) ⟨49250, by rfl⟩ : syracuseStep 1050677 = 98501) (by norm_num)
theorem B1574981 : Blo 698317 1574981 := bbase (se 4 (by rfl) ⟨147654, by rfl⟩ : syracuseStep 1574981 = 295309) (by norm_num)
theorem B1050701 : Blo 698317 1050701 := bbase (se 3 (by rfl) ⟨197006, by rfl⟩ : syracuseStep 1050701 = 394013) (by norm_num)
theorem B788557 : Blo 698317 788557 := bbase (se 3 (by rfl) ⟨147854, by rfl⟩ : syracuseStep 788557 = 295709) (by norm_num)
theorem B1050725 : Blo 698317 1050725 := bbase (se 4 (by rfl) ⟨98505, by rfl⟩ : syracuseStep 1050725 = 197011) (by norm_num)
theorem B886889 : Blo 698317 886889 := bbase (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) (by norm_num)
theorem B788593 : Blo 698317 788593 := bbase (se 2 (by rfl) ⟨295722, by rfl⟩ : syracuseStep 788593 = 591445) (by norm_num)
theorem B1050749 : Blo 698317 1050749 := bbase (se 3 (by rfl) ⟨197015, by rfl⟩ : syracuseStep 1050749 = 394031) (by norm_num)
theorem B1575053 : Blo 698317 1575053 := bbase (se 3 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 1575053 = 590645) (by norm_num)
theorem B1181837 : Blo 698317 1181837 := bbase (se 3 (by rfl) ⟨221594, by rfl⟩ : syracuseStep 1181837 = 443189) (by norm_num)
theorem B1050773 : Blo 698317 1050773 := bbase (se 6 (by rfl) ⟨24627, by rfl⟩ : syracuseStep 1050773 = 49255) (by norm_num)
theorem B788629 : Blo 698317 788629 := bbase (se 6 (by rfl) ⟨18483, by rfl⟩ : syracuseStep 788629 = 36967) (by norm_num)
theorem B886945 : Blo 698317 886945 := bbase (se 2 (by rfl) ⟨332604, by rfl⟩ : syracuseStep 886945 = 665209) (by norm_num)
theorem B3541157 : Blo 698317 3541157 := bbase (se 4 (by rfl) ⟨331983, by rfl⟩ : syracuseStep 3541157 = 663967) (by norm_num)
theorem B1050797 : Blo 698317 1050797 := bbase (se 3 (by rfl) ⟨197024, by rfl⟩ : syracuseStep 1050797 = 394049) (by norm_num)
theorem B788665 : Blo 698317 788665 := bbase (se 2 (by rfl) ⟨295749, by rfl⟩ : syracuseStep 788665 = 591499) (by norm_num)
theorem B1050821 : Blo 698317 1050821 := bbase (se 4 (by rfl) ⟨98514, by rfl⟩ : syracuseStep 1050821 = 197029) (by norm_num)
theorem B1771733 : Blo 698317 1771733 := bbase (se 7 (by rfl) ⟨20762, by rfl⟩ : syracuseStep 1771733 = 41525) (by norm_num)
theorem B1575125 : Blo 698317 1575125 := bbase (se 7 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 1575125 = 36917) (by norm_num)
theorem B5998805 : Blo 698317 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B1050845 : Blo 698317 1050845 := bbase (se 3 (by rfl) ⟨197033, by rfl⟩ : syracuseStep 1050845 = 394067) (by norm_num)
theorem B788701 : Blo 698317 788701 := bbase (se 3 (by rfl) ⟨147881, by rfl⟩ : syracuseStep 788701 = 295763) (by norm_num)
theorem B1050869 : Blo 698317 1050869 := bbase (se 5 (by rfl) ⟨49259, by rfl⟩ : syracuseStep 1050869 = 98519) (by norm_num)
theorem B887041 : Blo 698317 887041 := bbase (se 2 (by rfl) ⟨332640, by rfl⟩ : syracuseStep 887041 = 665281) (by norm_num)
theorem B788737 : Blo 698317 788737 := bbase (se 2 (by rfl) ⟨295776, by rfl⟩ : syracuseStep 788737 = 591553) (by norm_num)
theorem B1181965 : Blo 698317 1181965 := bbase (se 3 (by rfl) ⟨221618, by rfl⟩ : syracuseStep 1181965 = 443237) (by norm_num)
theorem B1050893 : Blo 698317 1050893 := bbase (se 3 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 1050893 = 394085) (by norm_num)
theorem B1575197 : Blo 698317 1575197 := bbase (se 3 (by rfl) ⟨295349, by rfl⟩ : syracuseStep 1575197 = 590699) (by norm_num)
theorem B1050917 : Blo 698317 1050917 := bbase (se 4 (by rfl) ⟨98523, by rfl⟩ : syracuseStep 1050917 = 197047) (by norm_num)
theorem B788773 : Blo 698317 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B1050941 : Blo 698317 1050941 := bbase (se 3 (by rfl) ⟨197051, by rfl⟩ : syracuseStep 1050941 = 394103) (by norm_num)
theorem B788809 : Blo 698317 788809 := bbase (se 2 (by rfl) ⟨295803, by rfl⟩ : syracuseStep 788809 = 591607) (by norm_num)
theorem B2656597 : Blo 698317 2656597 := bbase (se 10 (by rfl) ⟨3891, by rfl⟩ : syracuseStep 2656597 = 7783) (by norm_num)
theorem B1050965 : Blo 698317 1050965 := bbase (se 10 (by rfl) ⟨1539, by rfl⟩ : syracuseStep 1050965 = 3079) (by norm_num)
theorem B1575269 : Blo 698317 1575269 := bbase (se 4 (by rfl) ⟨147681, by rfl⟩ : syracuseStep 1575269 = 295363) (by norm_num)
theorem B1182053 : Blo 698317 1182053 := bbase (se 4 (by rfl) ⟨110817, by rfl⟩ : syracuseStep 1182053 = 221635) (by norm_num)
theorem B1050989 : Blo 698317 1050989 := bbase (se 3 (by rfl) ⟨197060, by rfl⟩ : syracuseStep 1050989 = 394121) (by norm_num)
theorem B788845 : Blo 698317 788845 := bbase (se 3 (by rfl) ⟨147908, by rfl⟩ : syracuseStep 788845 = 295817) (by norm_num)
theorem B1051013 : Blo 698317 1051013 := bbase (se 4 (by rfl) ⟨98532, by rfl⟩ : syracuseStep 1051013 = 197065) (by norm_num)
theorem B788881 : Blo 698317 788881 := bbase (se 2 (by rfl) ⟨295830, by rfl⟩ : syracuseStep 788881 = 591661) (by norm_num)
theorem B1051037 : Blo 698317 1051037 := bbase (se 3 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 1051037 = 394139) (by norm_num)
theorem B1575341 : Blo 698317 1575341 := bbase (se 3 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 1575341 = 590753) (by norm_num)
theorem B887213 : Blo 698317 887213 := bbase (se 3 (by rfl) ⟨166352, by rfl⟩ : syracuseStep 887213 = 332705) (by norm_num)
theorem B1051061 : Blo 698317 1051061 := bbase (se 5 (by rfl) ⟨49268, by rfl⟩ : syracuseStep 1051061 = 98537) (by norm_num)
theorem B788917 : Blo 698317 788917 := bbase (se 5 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 788917 = 73961) (by norm_num)
theorem B2361797 : Blo 698317 2361797 := bbase (se 4 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 2361797 = 442837) (by norm_num)
theorem B1051085 : Blo 698317 1051085 := bbase (se 3 (by rfl) ⟨197078, by rfl⟩ : syracuseStep 1051085 = 394157) (by norm_num)
theorem B788953 : Blo 698317 788953 := bbase (se 2 (by rfl) ⟨295857, by rfl⟩ : syracuseStep 788953 = 591715) (by norm_num)
theorem B1182181 : Blo 698317 1182181 := bbase (se 4 (by rfl) ⟨110829, by rfl⟩ : syracuseStep 1182181 = 221659) (by norm_num)
theorem B1051109 : Blo 698317 1051109 := bbase (se 4 (by rfl) ⟨98541, by rfl⟩ : syracuseStep 1051109 = 197083) (by norm_num)
theorem B887269 : Blo 698317 887269 := bbase (se 4 (by rfl) ⟨83181, by rfl⟩ : syracuseStep 887269 = 166363) (by norm_num)
theorem B1575413 : Blo 698317 1575413 := bbase (se 5 (by rfl) ⟨73847, by rfl⟩ : syracuseStep 1575413 = 147695) (by norm_num)
theorem B1051133 : Blo 698317 1051133 := bbase (se 3 (by rfl) ⟨197087, by rfl⟩ : syracuseStep 1051133 = 394175) (by norm_num)
theorem B788989 : Blo 698317 788989 := bbase (se 3 (by rfl) ⟨147935, by rfl⟩ : syracuseStep 788989 = 295871) (by norm_num)
theorem B1051157 : Blo 698317 1051157 := bbase (se 6 (by rfl) ⟨24636, by rfl⟩ : syracuseStep 1051157 = 49273) (by norm_num)
theorem B789025 : Blo 698317 789025 := bbase (se 2 (by rfl) ⟨295884, by rfl⟩ : syracuseStep 789025 = 591769) (by norm_num)
theorem B1772077 : Blo 698317 1772077 := bbase (se 3 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 1772077 = 664529) (by norm_num)
theorem B1051181 : Blo 698317 1051181 := bbase (se 3 (by rfl) ⟨197096, by rfl⟩ : syracuseStep 1051181 = 394193) (by norm_num)
theorem B1575485 : Blo 698317 1575485 := bbase (se 3 (by rfl) ⟨295403, by rfl⟩ : syracuseStep 1575485 = 590807) (by norm_num)
theorem B1182269 : Blo 698317 1182269 := bbase (se 3 (by rfl) ⟨221675, by rfl⟩ : syracuseStep 1182269 = 443351) (by norm_num)
theorem B1051205 : Blo 698317 1051205 := bbase (se 4 (by rfl) ⟨98550, by rfl⟩ : syracuseStep 1051205 = 197101) (by norm_num)
theorem B887365 : Blo 698317 887365 := bbase (se 4 (by rfl) ⟨83190, by rfl⟩ : syracuseStep 887365 = 166381) (by norm_num)
theorem B789061 : Blo 698317 789061 := bbase (se 4 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 789061 = 147949) (by norm_num)
theorem B1051229 : Blo 698317 1051229 := bbase (se 3 (by rfl) ⟨197105, by rfl⟩ : syracuseStep 1051229 = 394211) (by norm_num)
theorem B789097 : Blo 698317 789097 := bbase (se 2 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 789097 = 591823) (by norm_num)
theorem B1051253 : Blo 698317 1051253 := bbase (se 5 (by rfl) ⟨49277, by rfl⟩ : syracuseStep 1051253 = 98555) (by norm_num)
theorem B2656901 : Blo 698317 2656901 := bbase (se 4 (by rfl) ⟨249084, by rfl⟩ : syracuseStep 2656901 = 498169) (by norm_num)
theorem B1575557 : Blo 698317 1575557 := bbase (se 4 (by rfl) ⟨147708, by rfl⟩ : syracuseStep 1575557 = 295417) (by norm_num)
theorem B1051277 : Blo 698317 1051277 := bbase (se 3 (by rfl) ⟨197114, by rfl⟩ : syracuseStep 1051277 = 394229) (by norm_num)
theorem B789133 : Blo 698317 789133 := bbase (se 3 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 789133 = 295925) (by norm_num)
theorem B2525845 : Blo 698317 2525845 := bbase (se 6 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 2525845 = 118399) (by norm_num)
theorem B1772189 : Blo 698317 1772189 := bbase (se 3 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 1772189 = 664571) (by norm_num)
theorem B1051301 : Blo 698317 1051301 := bbase (se 4 (by rfl) ⟨98559, by rfl⟩ : syracuseStep 1051301 = 197119) (by norm_num)
theorem B789169 : Blo 698317 789169 := bbase (se 2 (by rfl) ⟨295938, by rfl⟩ : syracuseStep 789169 = 591877) (by norm_num)
theorem B1182397 : Blo 698317 1182397 := bbase (se 3 (by rfl) ⟨221699, by rfl⟩ : syracuseStep 1182397 = 443399) (by norm_num)
theorem B1051325 : Blo 698317 1051325 := bbase (se 3 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 1051325 = 394247) (by norm_num)
theorem B1575629 : Blo 698317 1575629 := bbase (se 3 (by rfl) ⟨295430, by rfl⟩ : syracuseStep 1575629 = 590861) (by norm_num)
theorem B1051349 : Blo 698317 1051349 := bbase (se 7 (by rfl) ⟨12320, by rfl⟩ : syracuseStep 1051349 = 24641) (by norm_num)
theorem B789205 : Blo 698317 789205 := bbase (se 7 (by rfl) ⟨9248, by rfl⟩ : syracuseStep 789205 = 18497) (by norm_num)
theorem B1051373 : Blo 698317 1051373 := bbase (se 3 (by rfl) ⟨197132, by rfl⟩ : syracuseStep 1051373 = 394265) (by norm_num)
theorem B887537 : Blo 698317 887537 := bbase (se 2 (by rfl) ⟨332826, by rfl⟩ : syracuseStep 887537 = 665653) (by norm_num)
theorem B789241 : Blo 698317 789241 := bbase (se 2 (by rfl) ⟨295965, by rfl⟩ : syracuseStep 789241 = 591931) (by norm_num)
theorem B1051397 : Blo 698317 1051397 := bbase (se 4 (by rfl) ⟨98568, by rfl⟩ : syracuseStep 1051397 = 197137) (by norm_num)
theorem B1575701 : Blo 698317 1575701 := bbase (se 6 (by rfl) ⟨36930, by rfl⟩ : syracuseStep 1575701 = 73861) (by norm_num)
theorem B1182485 : Blo 698317 1182485 := bbase (se 6 (by rfl) ⟨27714, by rfl⟩ : syracuseStep 1182485 = 55429) (by norm_num)
theorem B1051421 : Blo 698317 1051421 := bbase (se 3 (by rfl) ⟨197141, by rfl⟩ : syracuseStep 1051421 = 394283) (by norm_num)
theorem B789277 : Blo 698317 789277 := bbase (se 3 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 789277 = 295979) (by norm_num)
theorem B887593 : Blo 698317 887593 := bbase (se 2 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 887593 = 665695) (by norm_num)
theorem B1051445 : Blo 698317 1051445 := bbase (se 5 (by rfl) ⟨49286, by rfl⟩ : syracuseStep 1051445 = 98573) (by norm_num)
theorem B789313 : Blo 698317 789313 := bbase (se 2 (by rfl) ⟨295992, by rfl⟩ : syracuseStep 789313 = 591985) (by norm_num)
theorem B1051469 : Blo 698317 1051469 := bbase (se 3 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 1051469 = 394301) (by norm_num)
theorem B1772381 : Blo 698317 1772381 := bbase (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) (by norm_num)
theorem B1575773 : Blo 698317 1575773 := bbase (se 3 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 1575773 = 590915) (by norm_num)
theorem B1051493 : Blo 698317 1051493 := bbase (se 4 (by rfl) ⟨98577, by rfl⟩ : syracuseStep 1051493 = 197155) (by norm_num)
theorem B2132837 : Blo 698317 2132837 := bbase (se 4 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 2132837 = 399907) (by norm_num)
theorem B789349 : Blo 698317 789349 := bbase (se 4 (by rfl) ⟨74001, by rfl⟩ : syracuseStep 789349 = 148003) (by norm_num)
theorem B2362229 : Blo 698317 2362229 := bbase (se 5 (by rfl) ⟨110729, by rfl⟩ : syracuseStep 2362229 = 221459) (by norm_num)
theorem B1051517 : Blo 698317 1051517 := bbase (se 3 (by rfl) ⟨197159, by rfl⟩ : syracuseStep 1051517 = 394319) (by norm_num)
theorem B887689 : Blo 698317 887689 := bbase (se 2 (by rfl) ⟨332883, by rfl⟩ : syracuseStep 887689 = 665767) (by norm_num)
theorem B789385 : Blo 698317 789385 := bbase (se 2 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 789385 = 592039) (by norm_num)
theorem B1182613 : Blo 698317 1182613 := bbase (se 6 (by rfl) ⟨27717, by rfl⟩ : syracuseStep 1182613 = 55435) (by norm_num)
theorem B1051541 : Blo 698317 1051541 := bbase (se 6 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 1051541 = 49291) (by norm_num)
theorem B1575845 : Blo 698317 1575845 := bbase (se 4 (by rfl) ⟨147735, by rfl⟩ : syracuseStep 1575845 = 295471) (by norm_num)
theorem B1051565 : Blo 698317 1051565 := bbase (se 3 (by rfl) ⟨197168, by rfl⟩ : syracuseStep 1051565 = 394337) (by norm_num)
theorem B789421 : Blo 698317 789421 := bbase (se 3 (by rfl) ⟨148016, by rfl⟩ : syracuseStep 789421 = 296033) (by norm_num)
theorem B1051589 : Blo 698317 1051589 := bbase (se 4 (by rfl) ⟨98586, by rfl⟩ : syracuseStep 1051589 = 197173) (by norm_num)
theorem B789457 : Blo 698317 789457 := bbase (se 2 (by rfl) ⟨296046, by rfl⟩ : syracuseStep 789457 = 592093) (by norm_num)
theorem B1051613 : Blo 698317 1051613 := bbase (se 3 (by rfl) ⟨197177, by rfl⟩ : syracuseStep 1051613 = 394355) (by norm_num)
theorem B1575917 : Blo 698317 1575917 := bbase (se 3 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 1575917 = 590969) (by norm_num)
theorem B1182701 : Blo 698317 1182701 := bbase (se 3 (by rfl) ⟨221756, by rfl⟩ : syracuseStep 1182701 = 443513) (by norm_num)
theorem B1051637 : Blo 698317 1051637 := bbase (se 5 (by rfl) ⟨49295, by rfl⟩ : syracuseStep 1051637 = 98591) (by norm_num)
theorem B789493 : Blo 698317 789493 := bbase (se 5 (by rfl) ⟨37007, by rfl⟩ : syracuseStep 789493 = 74015) (by norm_num)
theorem B1051661 : Blo 698317 1051661 := bbase (se 3 (by rfl) ⟨197186, by rfl⟩ : syracuseStep 1051661 = 394373) (by norm_num)
theorem B789529 : Blo 698317 789529 := bbase (se 2 (by rfl) ⟨296073, by rfl⟩ : syracuseStep 789529 = 592147) (by norm_num)
theorem B1051685 : Blo 698317 1051685 := bbase (se 4 (by rfl) ⟨98595, by rfl⟩ : syracuseStep 1051685 = 197191) (by norm_num)
theorem B1575989 : Blo 698317 1575989 := bbase (se 5 (by rfl) ⟨73874, by rfl⟩ : syracuseStep 1575989 = 147749) (by norm_num)
theorem B887861 : Blo 698317 887861 := bbase (se 5 (by rfl) ⟨41618, by rfl⟩ : syracuseStep 887861 = 83237) (by norm_num)
theorem B1051709 : Blo 698317 1051709 := bbase (se 3 (by rfl) ⟨197195, by rfl⟩ : syracuseStep 1051709 = 394391) (by norm_num)
theorem B789565 : Blo 698317 789565 := bbase (se 3 (by rfl) ⟨148043, by rfl⟩ : syracuseStep 789565 = 296087) (by norm_num)
theorem B1051733 : Blo 698317 1051733 := bbase (se 8 (by rfl) ⟨6162, by rfl⟩ : syracuseStep 1051733 = 12325) (by norm_num)
theorem B789601 : Blo 698317 789601 := bbase (se 2 (by rfl) ⟨296100, by rfl⟩ : syracuseStep 789601 = 592201) (by norm_num)
theorem B1182829 : Blo 698317 1182829 := bbase (se 3 (by rfl) ⟨221780, by rfl⟩ : syracuseStep 1182829 = 443561) (by norm_num)
theorem B1051757 : Blo 698317 1051757 := bbase (se 3 (by rfl) ⟨197204, by rfl⟩ : syracuseStep 1051757 = 394409) (by norm_num)
theorem B887917 : Blo 698317 887917 := bbase (se 3 (by rfl) ⟨166484, by rfl⟩ : syracuseStep 887917 = 332969) (by norm_num)
theorem B1576061 : Blo 698317 1576061 := bbase (se 3 (by rfl) ⟨295511, by rfl⟩ : syracuseStep 1576061 = 591023) (by norm_num)
theorem B1051781 : Blo 698317 1051781 := bbase (se 4 (by rfl) ⟨98604, by rfl⟩ : syracuseStep 1051781 = 197209) (by norm_num)
theorem B789637 : Blo 698317 789637 := bbase (se 4 (by rfl) ⟨74028, by rfl⟩ : syracuseStep 789637 = 148057) (by norm_num)
theorem B1051805 : Blo 698317 1051805 := bbase (se 3 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 1051805 = 394427) (by norm_num)
theorem B789673 : Blo 698317 789673 := bbase (se 2 (by rfl) ⟨296127, by rfl⟩ : syracuseStep 789673 = 592255) (by norm_num)
theorem B756913 : Blo 698317 756913 := bbase (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) (by norm_num)
theorem B1772725 : Blo 698317 1772725 := bbase (se 5 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 1772725 = 166193) (by norm_num)
theorem B1051829 : Blo 698317 1051829 := bbase (se 5 (by rfl) ⟨49304, by rfl⟩ : syracuseStep 1051829 = 98609) (by norm_num)
theorem B1576133 : Blo 698317 1576133 := bbase (se 4 (by rfl) ⟨147762, by rfl⟩ : syracuseStep 1576133 = 295525) (by norm_num)
theorem B1182917 : Blo 698317 1182917 := bbase (se 4 (by rfl) ⟨110898, by rfl⟩ : syracuseStep 1182917 = 221797) (by norm_num)
theorem B1051853 : Blo 698317 1051853 := bbase (se 3 (by rfl) ⟨197222, by rfl⟩ : syracuseStep 1051853 = 394445) (by norm_num)
theorem B888013 : Blo 698317 888013 := bbase (se 3 (by rfl) ⟨166502, by rfl⟩ : syracuseStep 888013 = 333005) (by norm_num)
theorem B789709 : Blo 698317 789709 := bbase (se 3 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 789709 = 296141) (by norm_num)
theorem B1051877 : Blo 698317 1051877 := bbase (se 4 (by rfl) ⟨98613, by rfl⟩ : syracuseStep 1051877 = 197227) (by norm_num)
theorem B789745 : Blo 698317 789745 := bbase (se 2 (by rfl) ⟨296154, by rfl⟩ : syracuseStep 789745 = 592309) (by norm_num)
theorem B1051901 : Blo 698317 1051901 := bbase (se 3 (by rfl) ⟨197231, by rfl⟩ : syracuseStep 1051901 = 394463) (by norm_num)
theorem B1576205 : Blo 698317 1576205 := bbase (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) (by norm_num)
theorem B1051925 : Blo 698317 1051925 := bbase (se 6 (by rfl) ⟨24654, by rfl⟩ : syracuseStep 1051925 = 49309) (by norm_num)
theorem B789781 : Blo 698317 789781 := bbase (se 6 (by rfl) ⟨18510, by rfl⟩ : syracuseStep 789781 = 37021) (by norm_num)
theorem B2362661 : Blo 698317 2362661 := bbase (se 4 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 2362661 = 442999) (by norm_num)
theorem B1772837 : Blo 698317 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B1051949 : Blo 698317 1051949 := bbase (se 3 (by rfl) ⟨197240, by rfl⟩ : syracuseStep 1051949 = 394481) (by norm_num)
theorem B789817 : Blo 698317 789817 := bbase (se 2 (by rfl) ⟨296181, by rfl⟩ : syracuseStep 789817 = 592363) (by norm_num)
theorem B1183045 : Blo 698317 1183045 := bbase (se 4 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 1183045 = 221821) (by norm_num)
theorem B1051973 : Blo 698317 1051973 := bbase (se 4 (by rfl) ⟨98622, by rfl⟩ : syracuseStep 1051973 = 197245) (by norm_num)
theorem B1576277 : Blo 698317 1576277 := bbase (se 11 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 1576277 = 2309) (by norm_num)
theorem B1051997 : Blo 698317 1051997 := bbase (se 3 (by rfl) ⟨197249, by rfl⟩ : syracuseStep 1051997 = 394499) (by norm_num)
theorem B789853 : Blo 698317 789853 := bbase (se 3 (by rfl) ⟨148097, by rfl⟩ : syracuseStep 789853 = 296195) (by norm_num)
theorem B1052021 : Blo 698317 1052021 := bbase (se 5 (by rfl) ⟨49313, by rfl⟩ : syracuseStep 1052021 = 98627) (by norm_num)
theorem B888185 : Blo 698317 888185 := bbase (se 2 (by rfl) ⟨333069, by rfl⟩ : syracuseStep 888185 = 666139) (by norm_num)
theorem B789889 : Blo 698317 789889 := bbase (se 2 (by rfl) ⟨296208, by rfl⟩ : syracuseStep 789889 = 592417) (by norm_num)
theorem B1052045 : Blo 698317 1052045 := bbase (se 3 (by rfl) ⟨197258, by rfl⟩ : syracuseStep 1052045 = 394517) (by norm_num)
theorem B1576349 : Blo 698317 1576349 := bbase (se 3 (by rfl) ⟨295565, by rfl⟩ : syracuseStep 1576349 = 591131) (by norm_num)
theorem B1183133 : Blo 698317 1183133 := bbase (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) (by norm_num)
theorem B1052069 : Blo 698317 1052069 := bbase (se 4 (by rfl) ⟨98631, by rfl⟩ : syracuseStep 1052069 = 197263) (by norm_num)
theorem B789925 : Blo 698317 789925 := bbase (se 4 (by rfl) ⟨74055, by rfl⟩ : syracuseStep 789925 = 148111) (by norm_num)
theorem B888241 : Blo 698317 888241 := bbase (se 2 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 888241 = 666181) (by norm_num)
theorem B3542453 : Blo 698317 3542453 := bbase (se 5 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 3542453 = 332105) (by norm_num)
theorem B1052093 : Blo 698317 1052093 := bbase (se 3 (by rfl) ⟨197267, by rfl⟩ : syracuseStep 1052093 = 394535) (by norm_num)
theorem B789961 : Blo 698317 789961 := bbase (se 2 (by rfl) ⟨296235, by rfl⟩ : syracuseStep 789961 = 592471) (by norm_num)
theorem B1052117 : Blo 698317 1052117 := bbase (se 7 (by rfl) ⟨12329, by rfl⟩ : syracuseStep 1052117 = 24659) (by norm_num)
theorem B1773029 : Blo 698317 1773029 := bbase (se 4 (by rfl) ⟨166221, by rfl⟩ : syracuseStep 1773029 = 332443) (by norm_num)
theorem B1576421 : Blo 698317 1576421 := bbase (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) (by norm_num)
theorem B1052141 : Blo 698317 1052141 := bbase (se 3 (by rfl) ⟨197276, by rfl⟩ : syracuseStep 1052141 = 394553) (by norm_num)
theorem B789997 : Blo 698317 789997 := bbase (se 3 (by rfl) ⟨148124, by rfl⟩ : syracuseStep 789997 = 296249) (by norm_num)
theorem B2985461 : Blo 698317 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B1052165 : Blo 698317 1052165 := bbase (se 4 (by rfl) ⟨98640, by rfl⟩ : syracuseStep 1052165 = 197281) (by norm_num)
theorem B888337 : Blo 698317 888337 := bbase (se 2 (by rfl) ⟨333126, by rfl⟩ : syracuseStep 888337 = 666253) (by norm_num)
theorem B790033 : Blo 698317 790033 := bbase (se 2 (by rfl) ⟨296262, by rfl⟩ : syracuseStep 790033 = 592525) (by norm_num)
theorem B1183261 : Blo 698317 1183261 := bbase (se 3 (by rfl) ⟨221861, by rfl⟩ : syracuseStep 1183261 = 443723) (by norm_num)
theorem B1052189 : Blo 698317 1052189 := bbase (se 3 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 1052189 = 394571) (by norm_num)
theorem B1576493 : Blo 698317 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B1052213 : Blo 698317 1052213 := bbase (se 5 (by rfl) ⟨49322, by rfl⟩ : syracuseStep 1052213 = 98645) (by norm_num)
theorem B790069 : Blo 698317 790069 := bbase (se 5 (by rfl) ⟨37034, by rfl⟩ : syracuseStep 790069 = 74069) (by norm_num)
theorem B1052237 : Blo 698317 1052237 := bbase (se 3 (by rfl) ⟨197294, by rfl⟩ : syracuseStep 1052237 = 394589) (by norm_num)
theorem B790105 : Blo 698317 790105 := bbase (se 2 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 790105 = 592579) (by norm_num)
theorem B1052261 : Blo 698317 1052261 := bbase (se 4 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 1052261 = 197299) (by norm_num)
theorem B1576565 : Blo 698317 1576565 := bbase (se 5 (by rfl) ⟨73901, by rfl⟩ : syracuseStep 1576565 = 147803) (by norm_num)
theorem B1183349 : Blo 698317 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B1052285 : Blo 698317 1052285 := bbase (se 3 (by rfl) ⟨197303, by rfl⟩ : syracuseStep 1052285 = 394607) (by norm_num)
theorem B1052309 : Blo 698317 1052309 := bbase (se 6 (by rfl) ⟨24663, by rfl⟩ : syracuseStep 1052309 = 49327) (by norm_num)
theorem B1052333 : Blo 698317 1052333 := bbase (se 3 (by rfl) ⟨197312, by rfl⟩ : syracuseStep 1052333 = 394625) (by norm_num)
theorem B1576637 : Blo 698317 1576637 := bbase (se 3 (by rfl) ⟨295619, by rfl⟩ : syracuseStep 1576637 = 591239) (by norm_num)
theorem B888509 : Blo 698317 888509 := bbase (se 3 (by rfl) ⟨166595, by rfl⟩ : syracuseStep 888509 = 333191) (by norm_num)
theorem B1052357 : Blo 698317 1052357 := bbase (se 4 (by rfl) ⟨98658, by rfl⟩ : syracuseStep 1052357 = 197317) (by norm_num)
theorem B2363093 : Blo 698317 2363093 := bbase (se 7 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 2363093 = 55385) (by norm_num)
theorem B1052381 : Blo 698317 1052381 := bbase (se 3 (by rfl) ⟨197321, by rfl⟩ : syracuseStep 1052381 = 394643) (by norm_num)
theorem B1183477 : Blo 698317 1183477 := bbase (se 5 (by rfl) ⟨55475, by rfl⟩ : syracuseStep 1183477 = 110951) (by norm_num)
theorem B1052405 : Blo 698317 1052405 := bbase (se 5 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 1052405 = 98663) (by norm_num)
theorem B888565 : Blo 698317 888565 := bbase (se 5 (by rfl) ⟨41651, by rfl⟩ : syracuseStep 888565 = 83303) (by norm_num)
theorem B1576709 : Blo 698317 1576709 := bbase (se 4 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 1576709 = 295633) (by norm_num)
theorem B1052429 : Blo 698317 1052429 := bbase (se 3 (by rfl) ⟨197330, by rfl⟩ : syracuseStep 1052429 = 394661) (by norm_num)
theorem B1052453 : Blo 698317 1052453 := bbase (se 4 (by rfl) ⟨98667, by rfl⟩ : syracuseStep 1052453 = 197335) (by norm_num)
theorem B1773373 : Blo 698317 1773373 := bbase (se 3 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 1773373 = 665015) (by norm_num)
theorem B1052477 : Blo 698317 1052477 := bbase (se 3 (by rfl) ⟨197339, by rfl⟩ : syracuseStep 1052477 = 394679) (by norm_num)
theorem B1576781 : Blo 698317 1576781 := bbase (se 3 (by rfl) ⟨295646, by rfl⟩ : syracuseStep 1576781 = 591293) (by norm_num)
theorem B1183565 : Blo 698317 1183565 := bbase (se 3 (by rfl) ⟨221918, by rfl⟩ : syracuseStep 1183565 = 443837) (by norm_num)
theorem B1052501 : Blo 698317 1052501 := bbase (se 9 (by rfl) ⟨3083, by rfl⟩ : syracuseStep 1052501 = 6167) (by norm_num)
theorem B888661 : Blo 698317 888661 := bbase (se 9 (by rfl) ⟨2603, by rfl⟩ : syracuseStep 888661 = 5207) (by norm_num)
theorem B1052525 : Blo 698317 1052525 := bbase (se 3 (by rfl) ⟨197348, by rfl⟩ : syracuseStep 1052525 = 394697) (by norm_num)
theorem B1052549 : Blo 698317 1052549 := bbase (se 4 (by rfl) ⟨98676, by rfl⟩ : syracuseStep 1052549 = 197353) (by norm_num)
theorem B1576853 : Blo 698317 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B1052573 : Blo 698317 1052573 := bbase (se 3 (by rfl) ⟨197357, by rfl⟩ : syracuseStep 1052573 = 394715) (by norm_num)
theorem B1773485 : Blo 698317 1773485 := bbase (se 3 (by rfl) ⟨332528, by rfl⟩ : syracuseStep 1773485 = 665057) (by norm_num)
theorem B1052597 : Blo 698317 1052597 := bbase (se 5 (by rfl) ⟨49340, by rfl⟩ : syracuseStep 1052597 = 98681) (by norm_num)
theorem B1183693 : Blo 698317 1183693 := bbase (se 3 (by rfl) ⟨221942, by rfl⟩ : syracuseStep 1183693 = 443885) (by norm_num)
theorem B1052621 : Blo 698317 1052621 := bbase (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) (by norm_num)
theorem B1576925 : Blo 698317 1576925 := bbase (se 3 (by rfl) ⟨295673, by rfl⟩ : syracuseStep 1576925 = 591347) (by norm_num)
theorem B1052645 : Blo 698317 1052645 := bbase (se 4 (by rfl) ⟨98685, by rfl⟩ : syracuseStep 1052645 = 197371) (by norm_num)
theorem B1052669 : Blo 698317 1052669 := bbase (se 3 (by rfl) ⟨197375, by rfl⟩ : syracuseStep 1052669 = 394751) (by norm_num)
theorem B888833 : Blo 698317 888833 := bbase (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) (by norm_num)
theorem B1052693 : Blo 698317 1052693 := bbase (se 6 (by rfl) ⟨24672, by rfl⟩ : syracuseStep 1052693 = 49345) (by norm_num)
theorem B1576997 : Blo 698317 1576997 := bbase (se 4 (by rfl) ⟨147843, by rfl⟩ : syracuseStep 1576997 = 295687) (by norm_num)
theorem B1183781 : Blo 698317 1183781 := bbase (se 4 (by rfl) ⟨110979, by rfl⟩ : syracuseStep 1183781 = 221959) (by norm_num)
theorem B1052717 : Blo 698317 1052717 := bbase (se 3 (by rfl) ⟨197384, by rfl⟩ : syracuseStep 1052717 = 394769) (by norm_num)
theorem B5050421 : Blo 698317 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B1052741 : Blo 698317 1052741 := bbase (se 4 (by rfl) ⟨98694, by rfl⟩ : syracuseStep 1052741 = 197389) (by norm_num)
theorem B1052765 : Blo 698317 1052765 := bbase (se 3 (by rfl) ⟨197393, by rfl⟩ : syracuseStep 1052765 = 394787) (by norm_num)
theorem B1773677 : Blo 698317 1773677 := bbase (se 3 (by rfl) ⟨332564, by rfl⟩ : syracuseStep 1773677 = 665129) (by norm_num)
theorem B1577069 : Blo 698317 1577069 := bbase (se 3 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 1577069 = 591401) (by norm_num)
theorem B1052789 : Blo 698317 1052789 := bbase (se 5 (by rfl) ⟨49349, by rfl⟩ : syracuseStep 1052789 = 98699) (by norm_num)
theorem B2363525 : Blo 698317 2363525 := bbase (se 4 (by rfl) ⟨221580, by rfl⟩ : syracuseStep 2363525 = 443161) (by norm_num)
theorem B1052813 : Blo 698317 1052813 := bbase (se 3 (by rfl) ⟨197402, by rfl⟩ : syracuseStep 1052813 = 394805) (by norm_num)
theorem B1183909 : Blo 698317 1183909 := bbase (se 4 (by rfl) ⟨110991, by rfl⟩ : syracuseStep 1183909 = 221983) (by norm_num)
theorem B1052837 : Blo 698317 1052837 := bbase (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) (by norm_num)
theorem B1577141 : Blo 698317 1577141 := bbase (se 5 (by rfl) ⟨73928, by rfl⟩ : syracuseStep 1577141 = 147857) (by norm_num)
theorem B1052861 : Blo 698317 1052861 := bbase (se 3 (by rfl) ⟨197411, by rfl⟩ : syracuseStep 1052861 = 394823) (by norm_num)
theorem B1052885 : Blo 698317 1052885 := bbase (se 7 (by rfl) ⟨12338, by rfl⟩ : syracuseStep 1052885 = 24677) (by norm_num)
theorem B1052909 : Blo 698317 1052909 := bbase (se 3 (by rfl) ⟨197420, by rfl⟩ : syracuseStep 1052909 = 394841) (by norm_num)
theorem B1577213 : Blo 698317 1577213 := bbase (se 3 (by rfl) ⟨295727, by rfl⟩ : syracuseStep 1577213 = 591455) (by norm_num)
theorem B1183997 : Blo 698317 1183997 := bbase (se 3 (by rfl) ⟨221999, by rfl⟩ : syracuseStep 1183997 = 443999) (by norm_num)
theorem B1052933 : Blo 698317 1052933 := bbase (se 4 (by rfl) ⟨98712, by rfl⟩ : syracuseStep 1052933 = 197425) (by norm_num)
theorem B1052957 : Blo 698317 1052957 := bbase (se 3 (by rfl) ⟨197429, by rfl⟩ : syracuseStep 1052957 = 394859) (by norm_num)
theorem B1052981 : Blo 698317 1052981 := bbase (se 5 (by rfl) ⟨49358, by rfl⟩ : syracuseStep 1052981 = 98717) (by norm_num)
theorem B1577285 : Blo 698317 1577285 := bbase (se 4 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 1577285 = 295741) (by norm_num)
theorem B1053005 : Blo 698317 1053005 := bbase (se 3 (by rfl) ⟨197438, by rfl⟩ : syracuseStep 1053005 = 394877) (by norm_num)
theorem B1053029 : Blo 698317 1053029 := bbase (se 4 (by rfl) ⟨98721, by rfl⟩ : syracuseStep 1053029 = 197443) (by norm_num)
theorem B1184125 : Blo 698317 1184125 := bbase (se 3 (by rfl) ⟨222023, by rfl⟩ : syracuseStep 1184125 = 444047) (by norm_num)
theorem B1053053 : Blo 698317 1053053 := bbase (se 3 (by rfl) ⟨197447, by rfl⟩ : syracuseStep 1053053 = 394895) (by norm_num)
theorem B1577357 : Blo 698317 1577357 := bbase (se 3 (by rfl) ⟨295754, by rfl⟩ : syracuseStep 1577357 = 591509) (by norm_num)
theorem B1053077 : Blo 698317 1053077 := bbase (se 6 (by rfl) ⟨24681, by rfl⟩ : syracuseStep 1053077 = 49363) (by norm_num)
theorem B1053101 : Blo 698317 1053101 := bbase (se 3 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 1053101 = 394913) (by norm_num)
theorem B1774021 : Blo 698317 1774021 := bbase (se 4 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 1774021 = 332629) (by norm_num)
theorem B1053125 : Blo 698317 1053125 := bbase (se 4 (by rfl) ⟨98730, by rfl⟩ : syracuseStep 1053125 = 197461) (by norm_num)
theorem B1577429 : Blo 698317 1577429 := bbase (se 7 (by rfl) ⟨18485, by rfl⟩ : syracuseStep 1577429 = 36971) (by norm_num)
theorem B1184213 : Blo 698317 1184213 := bbase (se 7 (by rfl) ⟨13877, by rfl⟩ : syracuseStep 1184213 = 27755) (by norm_num)
theorem B1053149 : Blo 698317 1053149 := bbase (se 3 (by rfl) ⟨197465, by rfl⟩ : syracuseStep 1053149 = 394931) (by norm_num)
theorem B1053173 : Blo 698317 1053173 := bbase (se 5 (by rfl) ⟨49367, by rfl⟩ : syracuseStep 1053173 = 98735) (by norm_num)
theorem B1053197 : Blo 698317 1053197 := bbase (se 3 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 1053197 = 394949) (by norm_num)
theorem B1577501 : Blo 698317 1577501 := bbase (se 3 (by rfl) ⟨295781, by rfl⟩ : syracuseStep 1577501 = 591563) (by norm_num)
theorem B1053221 : Blo 698317 1053221 := bbase (se 4 (by rfl) ⟨98739, by rfl⟩ : syracuseStep 1053221 = 197479) (by norm_num)
theorem B2363957 : Blo 698317 2363957 := bbase (se 5 (by rfl) ⟨110810, by rfl⟩ : syracuseStep 2363957 = 221621) (by norm_num)
theorem B1774133 : Blo 698317 1774133 := bbase (se 5 (by rfl) ⟨83162, by rfl⟩ : syracuseStep 1774133 = 166325) (by norm_num)
theorem B1053245 : Blo 698317 1053245 := bbase (se 3 (by rfl) ⟨197483, by rfl⟩ : syracuseStep 1053245 = 394967) (by norm_num)
theorem B1184341 : Blo 698317 1184341 := bbase (se 8 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 1184341 = 13879) (by norm_num)
theorem B1053269 : Blo 698317 1053269 := bbase (se 8 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 1053269 = 12343) (by norm_num)
theorem B1577573 : Blo 698317 1577573 := bbase (se 4 (by rfl) ⟨147897, by rfl⟩ : syracuseStep 1577573 = 295795) (by norm_num)
theorem B1053293 : Blo 698317 1053293 := bbase (se 3 (by rfl) ⟨197492, by rfl⟩ : syracuseStep 1053293 = 394985) (by norm_num)
theorem B1053317 : Blo 698317 1053317 := bbase (se 4 (by rfl) ⟨98748, by rfl⟩ : syracuseStep 1053317 = 197497) (by norm_num)
theorem B1217173 : Blo 698317 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1053341 : Blo 698317 1053341 := bbase (se 3 (by rfl) ⟨197501, by rfl⟩ : syracuseStep 1053341 = 395003) (by norm_num)
theorem B1577645 : Blo 698317 1577645 := bbase (se 3 (by rfl) ⟨295808, by rfl⟩ : syracuseStep 1577645 = 591617) (by norm_num)
theorem B1184429 : Blo 698317 1184429 := bbase (se 3 (by rfl) ⟨222080, by rfl⟩ : syracuseStep 1184429 = 444161) (by norm_num)
theorem B5968565 : Blo 698317 5968565 := bbase (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) (by norm_num)
theorem B1053365 : Blo 698317 1053365 := bbase (se 5 (by rfl) ⟨49376, by rfl⟩ : syracuseStep 1053365 = 98753) (by norm_num)
theorem B3543749 : Blo 698317 3543749 := bbase (se 4 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 3543749 = 664453) (by norm_num)
theorem B2659013 : Blo 698317 2659013 := bbase (se 4 (by rfl) ⟨249282, by rfl⟩ : syracuseStep 2659013 = 498565) (by norm_num)
theorem B1053389 : Blo 698317 1053389 := bbase (se 3 (by rfl) ⟨197510, by rfl⟩ : syracuseStep 1053389 = 395021) (by norm_num)
theorem B1053413 : Blo 698317 1053413 := bbase (se 4 (by rfl) ⟨98757, by rfl⟩ : syracuseStep 1053413 = 197515) (by norm_num)
theorem B1774325 : Blo 698317 1774325 := bbase (se 5 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 1774325 = 166343) (by norm_num)
theorem B1577717 : Blo 698317 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B1053437 : Blo 698317 1053437 := bbase (se 3 (by rfl) ⟨197519, by rfl⟩ : syracuseStep 1053437 = 395039) (by norm_num)
theorem B1053461 : Blo 698317 1053461 := bbase (se 6 (by rfl) ⟨24690, by rfl⟩ : syracuseStep 1053461 = 49381) (by norm_num)
theorem B1184557 : Blo 698317 1184557 := bbase (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) (by norm_num)
theorem B1577789 : Blo 698317 1577789 := bbase (se 3 (by rfl) ⟨295835, by rfl⟩ : syracuseStep 1577789 = 591671) (by norm_num)
theorem B9835349 : Blo 698317 9835349 := bbase (se 9 (by rfl) ⟨28814, by rfl⟩ : syracuseStep 9835349 = 57629) (by norm_num)
theorem B1577861 : Blo 698317 1577861 := bbase (se 4 (by rfl) ⟨147924, by rfl⟩ : syracuseStep 1577861 = 295849) (by norm_num)
theorem B1184645 : Blo 698317 1184645 := bbase (se 4 (by rfl) ⟨111060, by rfl⟩ : syracuseStep 1184645 = 222121) (by norm_num)
theorem B1577933 : Blo 698317 1577933 := bbase (se 3 (by rfl) ⟨295862, by rfl⟩ : syracuseStep 1577933 = 591725) (by norm_num)
theorem B2659301 : Blo 698317 2659301 := bbase (se 4 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 2659301 = 498619) (by norm_num)
theorem B2364389 : Blo 698317 2364389 := bbase (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) (by norm_num)
theorem B1184773 : Blo 698317 1184773 := bbase (se 4 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 1184773 = 222145) (by norm_num)
theorem B1578005 : Blo 698317 1578005 := bbase (se 6 (by rfl) ⟨36984, by rfl⟩ : syracuseStep 1578005 = 73969) (by norm_num)
theorem B1774669 : Blo 698317 1774669 := bbase (se 3 (by rfl) ⟨332750, by rfl⟩ : syracuseStep 1774669 = 665501) (by norm_num)
theorem B1119317 : Blo 698317 1119317 := bbase (se 8 (by rfl) ⟨6558, by rfl⟩ : syracuseStep 1119317 = 13117) (by norm_num)
theorem B1578077 : Blo 698317 1578077 := bbase (se 3 (by rfl) ⟨295889, by rfl⟩ : syracuseStep 1578077 = 591779) (by norm_num)
theorem B1184861 : Blo 698317 1184861 := bbase (se 3 (by rfl) ⟨222161, by rfl⟩ : syracuseStep 1184861 = 444323) (by norm_num)
theorem B2135173 : Blo 698317 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B1578149 : Blo 698317 1578149 := bbase (se 4 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 1578149 = 295903) (by norm_num)
theorem B1774781 : Blo 698317 1774781 := bbase (se 3 (by rfl) ⟨332771, by rfl⟩ : syracuseStep 1774781 = 665543) (by norm_num)
theorem B1184989 : Blo 698317 1184989 := bbase (se 3 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 1184989 = 444371) (by norm_num)
theorem B1578221 : Blo 698317 1578221 := bbase (se 3 (by rfl) ⟨295916, by rfl⟩ : syracuseStep 1578221 = 591833) (by norm_num)
theorem B1578293 : Blo 698317 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B1185077 : Blo 698317 1185077 := bbase (se 5 (by rfl) ⟨55550, by rfl⟩ : syracuseStep 1185077 = 111101) (by norm_num)
theorem B1774973 : Blo 698317 1774973 := bbase (se 3 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 1774973 = 665615) (by norm_num)
theorem B1578365 : Blo 698317 1578365 := bbase (se 3 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 1578365 = 591887) (by norm_num)
theorem B2364821 : Blo 698317 2364821 := bbase (se 6 (by rfl) ⟨55425, by rfl⟩ : syracuseStep 2364821 = 110851) (by norm_num)
theorem B1578437 : Blo 698317 1578437 := bbase (se 4 (by rfl) ⟨147978, by rfl⟩ : syracuseStep 1578437 = 295957) (by norm_num)
theorem B1578509 : Blo 698317 1578509 := bbase (se 3 (by rfl) ⟨295970, by rfl⟩ : syracuseStep 1578509 = 591941) (by norm_num)
theorem B1578581 : Blo 698317 1578581 := bbase (se 8 (by rfl) ⟨9249, by rfl⟩ : syracuseStep 1578581 = 18499) (by norm_num)
theorem B2692709 : Blo 698317 2692709 := bbase (se 4 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 2692709 = 504883) (by norm_num)
theorem B1578653 : Blo 698317 1578653 := bbase (se 3 (by rfl) ⟨295997, by rfl⟩ : syracuseStep 1578653 = 591995) (by norm_num)
theorem B1775317 : Blo 698317 1775317 := bbase (se 7 (by rfl) ⟨20804, by rfl⟩ : syracuseStep 1775317 = 41609) (by norm_num)
theorem B1578725 : Blo 698317 1578725 := bbase (se 4 (by rfl) ⟨148005, by rfl⟩ : syracuseStep 1578725 = 296011) (by norm_num)
theorem B1119997 : Blo 698317 1119997 := bbase (se 3 (by rfl) ⟨209999, by rfl⟩ : syracuseStep 1119997 = 419999) (by norm_num)
theorem B1578797 : Blo 698317 1578797 := bbase (se 3 (by rfl) ⟨296024, by rfl⟩ : syracuseStep 1578797 = 592049) (by norm_num)
theorem B1120061 : Blo 698317 1120061 := bbase (se 3 (by rfl) ⟨210011, by rfl⟩ : syracuseStep 1120061 = 420023) (by norm_num)
theorem B2365253 : Blo 698317 2365253 := bbase (se 4 (by rfl) ⟨221742, by rfl⟩ : syracuseStep 2365253 = 443485) (by norm_num)
theorem B2561861 : Blo 698317 2561861 := bbase (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) (by norm_num)
theorem B1775429 : Blo 698317 1775429 := bbase (se 4 (by rfl) ⟨166446, by rfl⟩ : syracuseStep 1775429 = 332893) (by norm_num)
theorem B1513333 : Blo 698317 1513333 := bbase (se 5 (by rfl) ⟨70937, by rfl⟩ : syracuseStep 1513333 = 141875) (by norm_num)
theorem B1578869 : Blo 698317 1578869 := bbase (se 5 (by rfl) ⟨74009, by rfl⟩ : syracuseStep 1578869 = 148019) (by norm_num)
theorem B1578941 : Blo 698317 1578941 := bbase (se 3 (by rfl) ⟨296051, by rfl⟩ : syracuseStep 1578941 = 592103) (by norm_num)
theorem B3545045 : Blo 698317 3545045 := bbase (se 7 (by rfl) ⟨41543, by rfl⟩ : syracuseStep 3545045 = 83087) (by norm_num)
theorem B1775621 : Blo 698317 1775621 := bbase (se 4 (by rfl) ⟨166464, by rfl⟩ : syracuseStep 1775621 = 332929) (by norm_num)
theorem B1579013 : Blo 698317 1579013 := bbase (se 4 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 1579013 = 296065) (by norm_num)
theorem B1579085 : Blo 698317 1579085 := bbase (se 3 (by rfl) ⟨296078, by rfl⟩ : syracuseStep 1579085 = 592157) (by norm_num)
theorem B2660485 : Blo 698317 2660485 := bbase (se 4 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 2660485 = 498841) (by norm_num)
theorem B1579157 : Blo 698317 1579157 := bbase (se 6 (by rfl) ⟨37011, by rfl⟩ : syracuseStep 1579157 = 74023) (by norm_num)
theorem B1579229 : Blo 698317 1579229 := bbase (se 3 (by rfl) ⟨296105, by rfl⟩ : syracuseStep 1579229 = 592211) (by norm_num)
theorem B2365685 : Blo 698317 2365685 := bbase (se 5 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 2365685 = 221783) (by norm_num)
theorem B1579301 : Blo 698317 1579301 := bbase (se 4 (by rfl) ⟨148059, by rfl⟩ : syracuseStep 1579301 = 296119) (by norm_num)
theorem B1775965 : Blo 698317 1775965 := bbase (se 3 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 1775965 = 665987) (by norm_num)
theorem B1579373 : Blo 698317 1579373 := bbase (se 3 (by rfl) ⟨296132, by rfl⟩ : syracuseStep 1579373 = 592265) (by norm_num)
theorem B2660789 : Blo 698317 2660789 := bbase (se 5 (by rfl) ⟨124724, by rfl⟩ : syracuseStep 2660789 = 249449) (by norm_num)
theorem B1579445 : Blo 698317 1579445 := bbase (se 5 (by rfl) ⟨74036, by rfl⟩ : syracuseStep 1579445 = 148073) (by norm_num)
theorem B1776077 : Blo 698317 1776077 := bbase (se 3 (by rfl) ⟨333014, by rfl⟩ : syracuseStep 1776077 = 666029) (by norm_num)
theorem B1579517 : Blo 698317 1579517 := bbase (se 3 (by rfl) ⟨296159, by rfl⟩ : syracuseStep 1579517 = 592319) (by norm_num)
theorem B4495925 : Blo 698317 4495925 := bbase (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) (by norm_num)
theorem B1579589 : Blo 698317 1579589 := bbase (se 4 (by rfl) ⟨148086, by rfl⟩ : syracuseStep 1579589 = 296173) (by norm_num)
theorem B1776269 : Blo 698317 1776269 := bbase (se 3 (by rfl) ⟨333050, by rfl⟩ : syracuseStep 1776269 = 666101) (by norm_num)
theorem B1579661 : Blo 698317 1579661 := bbase (se 3 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 1579661 = 592373) (by norm_num)
theorem B2366117 : Blo 698317 2366117 := bbase (se 4 (by rfl) ⟨221823, by rfl⟩ : syracuseStep 2366117 = 443647) (by norm_num)
theorem B1579733 : Blo 698317 1579733 := bbase (se 7 (by rfl) ⟨18512, by rfl⟩ : syracuseStep 1579733 = 37025) (by norm_num)
theorem B1579805 : Blo 698317 1579805 := bbase (se 3 (by rfl) ⟨296213, by rfl⟩ : syracuseStep 1579805 = 592427) (by norm_num)
theorem B5315381 : Blo 698317 5315381 := bbase (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) (by norm_num)
theorem B1579877 : Blo 698317 1579877 := bbase (se 4 (by rfl) ⟨148113, by rfl⟩ : syracuseStep 1579877 = 296227) (by norm_num)
theorem B2399141 : Blo 698317 2399141 := bbase (se 4 (by rfl) ⟨224919, by rfl⟩ : syracuseStep 2399141 = 449839) (by norm_num)
theorem B1579949 : Blo 698317 1579949 := bbase (se 3 (by rfl) ⟨296240, by rfl⟩ : syracuseStep 1579949 = 592481) (by norm_num)
theorem B1776613 : Blo 698317 1776613 := bbase (se 4 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 1776613 = 333115) (by norm_num)
theorem B1580021 : Blo 698317 1580021 := bbase (se 5 (by rfl) ⟨74063, by rfl⟩ : syracuseStep 1580021 = 148127) (by norm_num)
theorem B1580093 : Blo 698317 1580093 := bbase (se 3 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 1580093 = 592535) (by norm_num)
theorem B2366549 : Blo 698317 2366549 := bbase (se 8 (by rfl) ⟨13866, by rfl⟩ : syracuseStep 2366549 = 27733) (by norm_num)
theorem B1776725 : Blo 698317 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B1121381 : Blo 698317 1121381 := bbase (se 4 (by rfl) ⟨105129, by rfl⟩ : syracuseStep 1121381 = 210259) (by norm_num)
theorem B1580165 : Blo 698317 1580165 := bbase (se 4 (by rfl) ⟨148140, by rfl⟩ : syracuseStep 1580165 = 296281) (by norm_num)
theorem B1678477 : Blo 698317 1678477 := bbase (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) (by norm_num)
theorem B3546341 : Blo 698317 3546341 := bbase (se 4 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 3546341 = 664939) (by norm_num)
theorem B1776917 : Blo 698317 1776917 := bbase (se 6 (by rfl) ⟨41646, by rfl⟩ : syracuseStep 1776917 = 83293) (by norm_num)
theorem B1121573 : Blo 698317 1121573 := bbase (se 4 (by rfl) ⟨105147, by rfl⟩ : syracuseStep 1121573 = 210295) (by norm_num)
theorem B1121701 : Blo 698317 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B2989493 : Blo 698317 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B1416701 : Blo 698317 1416701 := bbase (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) (by norm_num)
theorem B2366981 : Blo 698317 2366981 := bbase (se 4 (by rfl) ⟨221904, by rfl⟩ : syracuseStep 2366981 = 443809) (by norm_num)
theorem B3776053 : Blo 698317 3776053 := bbase (se 5 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 3776053 = 354005) (by norm_num)
theorem B1777261 : Blo 698317 1777261 := bbase (se 3 (by rfl) ⟨333236, by rfl⟩ : syracuseStep 1777261 = 666473) (by norm_num)
theorem B1777373 : Blo 698317 1777373 := bbase (se 3 (by rfl) ⟨333257, by rfl⟩ : syracuseStep 1777373 = 666515) (by norm_num)
theorem B925409 : Blo 698317 925409 := bbase (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) (by norm_num)
theorem B1679093 : Blo 698317 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B1777565 : Blo 698317 1777565 := bbase (se 3 (by rfl) ⟨333293, by rfl⟩ : syracuseStep 1777565 = 666587) (by norm_num)
theorem B2367413 : Blo 698317 2367413 := bbase (se 5 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 2367413 = 221945) (by norm_num)
theorem B1122341 : Blo 698317 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B1679429 : Blo 698317 1679429 := bbase (se 4 (by rfl) ⟨157446, by rfl⟩ : syracuseStep 1679429 = 314893) (by norm_num)
theorem B16162901 : Blo 698317 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B2367845 : Blo 698317 2367845 := bbase (se 4 (by rfl) ⟨221985, by rfl⟩ : syracuseStep 2367845 = 443971) (by norm_num)
theorem B1679821 : Blo 698317 1679821 := bbase (se 3 (by rfl) ⟨314966, by rfl⟩ : syracuseStep 1679821 = 629933) (by norm_num)
theorem B1515989 : Blo 698317 1515989 := bbase (se 7 (by rfl) ⟨17765, by rfl⟩ : syracuseStep 1515989 = 35531) (by norm_num)
theorem B1122797 : Blo 698317 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B3547637 : Blo 698317 3547637 := bbase (se 5 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 3547637 = 332591) (by norm_num)
theorem B2662901 : Blo 698317 2662901 := bbase (se 5 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 2662901 = 249647) (by norm_num)
theorem B1417837 : Blo 698317 1417837 := bbase (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) (by norm_num)
theorem B1123021 : Blo 698317 1123021 := bbase (se 3 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 1123021 = 421133) (by norm_num)
theorem B959197 : Blo 698317 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B1123085 : Blo 698317 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B2663189 : Blo 698317 2663189 := bbase (se 6 (by rfl) ⟨62418, by rfl⟩ : syracuseStep 2663189 = 124837) (by norm_num)
theorem B2368277 : Blo 698317 2368277 := bbase (se 6 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 2368277 = 111013) (by norm_num)
theorem B1123213 : Blo 698317 1123213 := bbase (se 3 (by rfl) ⟨210602, by rfl⟩ : syracuseStep 1123213 = 421205) (by norm_num)
theorem B2991269 : Blo 698317 2991269 := bbase (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) (by norm_num)
theorem B2368709 : Blo 698317 2368709 := bbase (se 4 (by rfl) ⟨222066, by rfl⟩ : syracuseStep 2368709 = 444133) (by norm_num)
theorem B4498901 : Blo 698317 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B2369141 : Blo 698317 2369141 := bbase (se 5 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 2369141 = 222107) (by norm_num)
theorem B7677589 : Blo 698317 7677589 := bbase (se 6 (by rfl) ⟨179943, by rfl⟩ : syracuseStep 7677589 = 359887) (by norm_num)
theorem B7186133 : Blo 698317 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B1419005 : Blo 698317 1419005 := bbase (se 3 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 1419005 = 532127) (by norm_num)
theorem B3548933 : Blo 698317 3548933 := bbase (se 4 (by rfl) ⟨332712, by rfl⟩ : syracuseStep 3548933 = 665425) (by norm_num)
theorem B1517429 : Blo 698317 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B2664373 : Blo 698317 2664373 := bbase (se 5 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 2664373 = 249785) (by norm_num)
theorem B796649 : Blo 698317 796649 := bbase (se 2 (by rfl) ⟨298743, by rfl⟩ : syracuseStep 796649 = 597487) (by norm_num)
theorem B2369573 : Blo 698317 2369573 := bbase (se 4 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 2369573 = 444295) (by norm_num)
theorem B3188821 : Blo 698317 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B1124437 : Blo 698317 1124437 := bbase (se 8 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 1124437 = 13177) (by norm_num)
theorem B2992261 : Blo 698317 2992261 := bbase (se 4 (by rfl) ⟨280524, by rfl⟩ : syracuseStep 2992261 = 561049) (by norm_num)
theorem B3188965 : Blo 698317 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B2664677 : Blo 698317 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B2370005 : Blo 698317 2370005 := bbase (se 7 (by rfl) ⟨27773, by rfl⟩ : syracuseStep 2370005 = 55547) (by norm_num)
theorem B2239301 : Blo 698317 2239301 := bbase (se 4 (by rfl) ⟨209934, by rfl⟩ : syracuseStep 2239301 = 419869) (by norm_num)
theorem B1518605 : Blo 698317 1518605 := bbase (se 3 (by rfl) ⟨284738, by rfl⟩ : syracuseStep 1518605 = 569477) (by norm_num)
theorem B3550229 : Blo 698317 3550229 := bbase (se 6 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 3550229 = 166417) (by norm_num)
theorem B10071317 : Blo 698317 10071317 := bbase (se 6 (by rfl) ⟨236046, by rfl⟩ : syracuseStep 10071317 = 472093) (by norm_num)
theorem B994789 : Blo 698317 994789 := bbase (se 4 (by rfl) ⟨93261, by rfl⟩ : syracuseStep 994789 = 186523) (by norm_num)
theorem B1682965 : Blo 698317 1682965 := bbase (se 6 (by rfl) ⟨39444, by rfl⟩ : syracuseStep 1682965 = 78889) (by norm_num)
theorem B1683013 : Blo 698317 1683013 := bbase (se 4 (by rfl) ⟨157782, by rfl⟩ : syracuseStep 1683013 = 315565) (by norm_num)
theorem B12136085 : Blo 698317 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B798373 : Blo 698317 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B798409 : Blo 698317 798409 := bbase (se 2 (by rfl) ⟨299403, by rfl⟩ : syracuseStep 798409 = 598807) (by norm_num)
theorem B10104533 : Blo 698317 10104533 := bbase (se 7 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 10104533 = 236825) (by norm_num)
theorem B3584101 : Blo 698317 3584101 := bbase (se 4 (by rfl) ⟨336009, by rfl⟩ : syracuseStep 3584101 = 672019) (by norm_num)
theorem B3977333 : Blo 698317 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B1683629 : Blo 698317 1683629 := bbase (se 3 (by rfl) ⟨315680, by rfl⟩ : syracuseStep 1683629 = 631361) (by norm_num)
theorem B1421501 : Blo 698317 1421501 := bbase (se 3 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 1421501 = 533063) (by norm_num)
theorem B995581 : Blo 698317 995581 := bbase (se 3 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 995581 = 373343) (by norm_num)
theorem B3551525 : Blo 698317 3551525 := bbase (se 4 (by rfl) ⟨332955, by rfl⟩ : syracuseStep 3551525 = 665911) (by norm_num)
theorem B897365 : Blo 698317 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B1683973 : Blo 698317 1683973 := bbase (se 4 (by rfl) ⟨157872, by rfl⟩ : syracuseStep 1683973 = 315745) (by norm_num)
theorem B864805 : Blo 698317 864805 := bbase (se 4 (by rfl) ⟨81075, by rfl⟩ : syracuseStep 864805 = 162151) (by norm_num)
theorem B995917 : Blo 698317 995917 := bbase (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) (by norm_num)
theorem B1421957 : Blo 698317 1421957 := bbase (se 4 (by rfl) ⟨133308, by rfl⟩ : syracuseStep 1421957 = 266617) (by norm_num)
theorem B1684205 : Blo 698317 1684205 := bbase (se 3 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 1684205 = 631577) (by norm_num)
theorem B2700053 : Blo 698317 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B996133 : Blo 698317 996133 := bbase (se 4 (by rfl) ⟨93387, by rfl⟩ : syracuseStep 996133 = 186775) (by norm_num)
theorem B1684397 : Blo 698317 1684397 := bbase (se 3 (by rfl) ⟨315824, by rfl⟩ : syracuseStep 1684397 = 631649) (by norm_num)
theorem B799741 : Blo 698317 799741 := bbase (se 3 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 799741 = 299903) (by norm_num)
theorem B2241557 : Blo 698317 2241557 := bbase (se 6 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 2241557 = 105073) (by norm_num)
theorem B996509 : Blo 698317 996509 := bbase (se 3 (by rfl) ⟨186845, by rfl⟩ : syracuseStep 996509 = 373691) (by norm_num)
theorem B2700485 : Blo 698317 2700485 := bbase (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) (by norm_num)
theorem B1684685 : Blo 698317 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B2831573 : Blo 698317 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B1062101 : Blo 698317 1062101 := bbase (se 7 (by rfl) ⟨12446, by rfl⟩ : syracuseStep 1062101 = 24893) (by norm_num)
theorem B3978517 : Blo 698317 3978517 := bbase (se 6 (by rfl) ⟨93246, by rfl⟩ : syracuseStep 3978517 = 186493) (by norm_num)
theorem B800069 : Blo 698317 800069 := bbase (se 4 (by rfl) ⟨75006, by rfl⟩ : syracuseStep 800069 = 150013) (by norm_num)
theorem B1062229 : Blo 698317 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B3552821 : Blo 698317 3552821 := bbase (se 5 (by rfl) ⟨166538, by rfl⟩ : syracuseStep 3552821 = 333077) (by norm_num)
theorem B6305365 : Blo 698317 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B3356261 : Blo 698317 3356261 := bbase (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) (by norm_num)
theorem B2242325 : Blo 698317 2242325 := bbase (se 6 (by rfl) ⟨52554, by rfl⟩ : syracuseStep 2242325 = 105109) (by norm_num)
theorem B3356453 : Blo 698317 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B800617 : Blo 698317 800617 := bbase (se 2 (by rfl) ⟨300231, by rfl⟩ : syracuseStep 800617 = 600463) (by norm_num)
theorem B2242837 : Blo 698317 2242837 := bbase (se 6 (by rfl) ⟨52566, by rfl⟩ : syracuseStep 2242837 = 105133) (by norm_num)
theorem B1259917 : Blo 698317 1259917 := bbase (se 3 (by rfl) ⟨236234, by rfl⟩ : syracuseStep 1259917 = 472469) (by norm_num)
theorem B5323157 : Blo 698317 5323157 := bbase (se 6 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 5323157 = 249523) (by norm_num)
theorem B7191061 : Blo 698317 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B997933 : Blo 698317 997933 := bbase (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) (by norm_num)
theorem B1325717 : Blo 698317 1325717 := bbase (se 6 (by rfl) ⟨31071, by rfl⟩ : syracuseStep 1325717 = 62143) (by norm_num)
theorem B3554117 : Blo 698317 3554117 := bbase (se 4 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 3554117 = 666397) (by norm_num)
theorem B7551893 : Blo 698317 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B1063949 : Blo 698317 1063949 := bbase (se 3 (by rfl) ⟨199490, by rfl⟩ : syracuseStep 1063949 = 398981) (by norm_num)
theorem B2997269 : Blo 698317 2997269 := bbase (se 6 (by rfl) ⟨70248, by rfl⟩ : syracuseStep 2997269 = 140497) (by norm_num)
theorem B998525 : Blo 698317 998525 := bbase (se 3 (by rfl) ⟨187223, by rfl⟩ : syracuseStep 998525 = 374447) (by norm_num)
theorem B998605 : Blo 698317 998605 := bbase (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) (by norm_num)
theorem B3980501 : Blo 698317 3980501 := bbase (se 7 (by rfl) ⟨46646, by rfl⟩ : syracuseStep 3980501 = 93293) (by norm_num)
theorem B7552277 : Blo 698317 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B2997557 : Blo 698317 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B998725 : Blo 698317 998725 := bbase (se 4 (by rfl) ⟨93630, by rfl⟩ : syracuseStep 998725 = 187261) (by norm_num)
theorem B7585109 : Blo 698317 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B1326469 : Blo 698317 1326469 := bbase (se 4 (by rfl) ⟨124356, by rfl⟩ : syracuseStep 1326469 = 248713) (by norm_num)
theorem B6733205 : Blo 698317 6733205 := bbase (se 6 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 6733205 = 315619) (by norm_num)
theorem B998821 : Blo 698317 998821 := bbase (se 4 (by rfl) ⟨93639, by rfl⟩ : syracuseStep 998821 = 187279) (by norm_num)
theorem B1326613 : Blo 698317 1326613 := bbase (se 6 (by rfl) ⟨31092, by rfl⟩ : syracuseStep 1326613 = 62185) (by norm_num)
theorem B1261165 : Blo 698317 1261165 := bbase (se 3 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 1261165 = 472937) (by norm_num)
theorem B1326773 : Blo 698317 1326773 := bbase (se 5 (by rfl) ⟨62192, by rfl⟩ : syracuseStep 1326773 = 124385) (by norm_num)
theorem B24592085 : Blo 698317 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B1326917 : Blo 698317 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B1261453 : Blo 698317 1261453 := bbase (se 3 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 1261453 = 473045) (by norm_num)
theorem B999317 : Blo 698317 999317 := bbase (se 6 (by rfl) ⟨23421, by rfl⟩ : syracuseStep 999317 = 46843) (by norm_num)
theorem B2244581 : Blo 698317 2244581 := bbase (se 4 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 2244581 = 420859) (by norm_num)
theorem B2998309 : Blo 698317 2998309 := bbase (se 4 (by rfl) ⟨281091, by rfl⟩ : syracuseStep 2998309 = 562183) (by norm_num)
theorem B3555413 : Blo 698317 3555413 := bbase (se 8 (by rfl) ⟨20832, by rfl⟩ : syracuseStep 3555413 = 41665) (by norm_num)
theorem B1327205 : Blo 698317 1327205 := bbase (se 4 (by rfl) ⟨124425, by rfl⟩ : syracuseStep 1327205 = 248851) (by norm_num)
theorem B1261669 : Blo 698317 1261669 := bbase (se 4 (by rfl) ⟨118281, by rfl⟩ : syracuseStep 1261669 = 236563) (by norm_num)
theorem B2244773 : Blo 698317 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B1327357 : Blo 698317 1327357 := bbase (se 3 (by rfl) ⟨248879, by rfl⟩ : syracuseStep 1327357 = 497759) (by norm_num)
theorem B999869 : Blo 698317 999869 := bbase (se 3 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 999869 = 374951) (by norm_num)
theorem B1327661 : Blo 698317 1327661 := bbase (se 3 (by rfl) ⟨248936, by rfl⟩ : syracuseStep 1327661 = 497873) (by norm_num)
theorem B1491637 : Blo 698317 1491637 := bbase (se 5 (by rfl) ⟨69920, by rfl⟩ : syracuseStep 1491637 = 139841) (by norm_num)
theorem B2999045 : Blo 698317 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B1262549 : Blo 698317 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B1492013 : Blo 698317 1492013 := bbase (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) (by norm_num)
theorem B1262765 : Blo 698317 1262765 := bbase (se 3 (by rfl) ⟨236768, by rfl⟩ : syracuseStep 1262765 = 473537) (by norm_num)
theorem B1328413 : Blo 698317 1328413 := bbase (se 3 (by rfl) ⟨249077, by rfl⟩ : syracuseStep 1328413 = 498155) (by norm_num)
theorem B1197421 : Blo 698317 1197421 := bbase (se 3 (by rfl) ⟨224516, by rfl⟩ : syracuseStep 1197421 = 449033) (by norm_num)
theorem B3982709 : Blo 698317 3982709 := bbase (se 5 (by rfl) ⟨186689, by rfl⟩ : syracuseStep 3982709 = 373379) (by norm_num)
theorem B1328557 : Blo 698317 1328557 := bbase (se 3 (by rfl) ⟨249104, by rfl⟩ : syracuseStep 1328557 = 498209) (by norm_num)
theorem B1263053 : Blo 698317 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B15123925 : Blo 698317 15123925 := bbase (se 7 (by rfl) ⟨177233, by rfl⟩ : syracuseStep 15123925 = 354467) (by norm_num)
theorem B1328717 : Blo 698317 1328717 := bbase (se 3 (by rfl) ⟨249134, by rfl⟩ : syracuseStep 1328717 = 498269) (by norm_num)
theorem B1328861 : Blo 698317 1328861 := bbase (se 3 (by rfl) ⟨249161, by rfl⟩ : syracuseStep 1328861 = 498323) (by norm_num)
theorem B3360565 : Blo 698317 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B1918853 : Blo 698317 1918853 := bbase (se 4 (by rfl) ⟨179892, by rfl⟩ : syracuseStep 1918853 = 359785) (by norm_num)
theorem B2836421 : Blo 698317 2836421 := bbase (se 4 (by rfl) ⟨265914, by rfl⟩ : syracuseStep 2836421 = 531829) (by norm_num)
theorem B1329149 : Blo 698317 1329149 := bbase (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) (by norm_num)
theorem B1329301 : Blo 698317 1329301 := bbase (se 6 (by rfl) ⟨31155, by rfl⟩ : syracuseStep 1329301 = 62311) (by norm_num)
theorem B1198237 : Blo 698317 1198237 := bbase (se 3 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 1198237 = 449339) (by norm_num)
theorem B1329605 : Blo 698317 1329605 := bbase (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) (by norm_num)
theorem B1264069 : Blo 698317 1264069 := bbase (se 4 (by rfl) ⟨118506, by rfl⟩ : syracuseStep 1264069 = 237013) (by norm_num)
theorem B1493653 : Blo 698317 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1199173 : Blo 698317 1199173 := bbase (se 4 (by rfl) ⟨112422, by rfl⟩ : syracuseStep 1199173 = 224845) (by norm_num)
theorem B1330357 : Blo 698317 1330357 := bbase (se 5 (by rfl) ⟨62360, by rfl⟩ : syracuseStep 1330357 = 124721) (by norm_num)
theorem B2837749 : Blo 698317 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B1330501 : Blo 698317 1330501 := bbase (se 4 (by rfl) ⟨124734, by rfl⟩ : syracuseStep 1330501 = 249469) (by norm_num)
theorem B7982549 : Blo 698317 7982549 := bbase (se 7 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 7982549 = 187091) (by norm_num)
theorem B1330661 : Blo 698317 1330661 := bbase (se 4 (by rfl) ⟨124749, by rfl⟩ : syracuseStep 1330661 = 249499) (by norm_num)
theorem B1494541 : Blo 698317 1494541 := bbase (se 3 (by rfl) ⟨280226, by rfl⟩ : syracuseStep 1494541 = 560453) (by norm_num)
theorem B1330805 : Blo 698317 1330805 := bbase (se 5 (by rfl) ⟨62381, by rfl⟩ : syracuseStep 1330805 = 124763) (by norm_num)
theorem B708221 : Blo 698317 708221 := bbase (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) (by norm_num)
theorem B2248373 : Blo 698317 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B1331093 : Blo 698317 1331093 := bbase (se 6 (by rfl) ⟨31197, by rfl⟩ : syracuseStep 1331093 = 62395) (by norm_num)
theorem B708545 : Blo 698317 708545 := bbase (se 2 (by rfl) ⟨265704, by rfl⟩ : syracuseStep 708545 = 531409) (by norm_num)
theorem B1495037 : Blo 698317 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1331245 : Blo 698317 1331245 := bbase (se 3 (by rfl) ⟨249608, by rfl⟩ : syracuseStep 1331245 = 499217) (by norm_num)
theorem B2019541 : Blo 698317 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B1593589 : Blo 698317 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B1331549 : Blo 698317 1331549 := bbase (se 3 (by rfl) ⟨249665, by rfl⟩ : syracuseStep 1331549 = 499331) (by norm_num)
theorem B5984725 : Blo 698317 5984725 := bbase (se 7 (by rfl) ⟨70133, by rfl⟩ : syracuseStep 5984725 = 140267) (by norm_num)
theorem B709093 : Blo 698317 709093 := bbase (se 4 (by rfl) ⟨66477, by rfl⟩ : syracuseStep 709093 = 132955) (by norm_num)
theorem B3330629 : Blo 698317 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B807545 : Blo 698317 807545 := bbase (se 2 (by rfl) ⟨302829, by rfl⟩ : syracuseStep 807545 = 605659) (by norm_num)
theorem B840353 : Blo 698317 840353 := bbase (se 2 (by rfl) ⟨315132, by rfl⟩ : syracuseStep 840353 = 630265) (by norm_num)
theorem B840449 : Blo 698317 840449 := bbase (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) (by norm_num)
theorem B1889045 : Blo 698317 1889045 := bbase (se 6 (by rfl) ⟨44274, by rfl⟩ : syracuseStep 1889045 = 88549) (by norm_num)
theorem B840469 : Blo 698317 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B4477781 : Blo 698317 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B1495901 : Blo 698317 1495901 := bbase (se 3 (by rfl) ⟨280481, by rfl⟩ : syracuseStep 1495901 = 560963) (by norm_num)
theorem B807841 : Blo 698317 807841 := bbase (se 2 (by rfl) ⟨302940, by rfl⟩ : syracuseStep 807841 = 605881) (by norm_num)
theorem B840613 : Blo 698317 840613 := bbase (se 4 (by rfl) ⟨78807, by rfl⟩ : syracuseStep 840613 = 157615) (by norm_num)
theorem B1496045 : Blo 698317 1496045 := bbase (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) (by norm_num)
theorem B1332301 : Blo 698317 1332301 := bbase (se 3 (by rfl) ⟨249806, by rfl⟩ : syracuseStep 1332301 = 499613) (by norm_num)
theorem B1332445 : Blo 698317 1332445 := bbase (se 3 (by rfl) ⟨249833, by rfl⟩ : syracuseStep 1332445 = 499667) (by norm_num)
theorem B3364085 : Blo 698317 3364085 := bbase (se 5 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 3364085 = 315383) (by norm_num)
theorem B1332605 : Blo 698317 1332605 := bbase (se 3 (by rfl) ⟨249863, by rfl⟩ : syracuseStep 1332605 = 499727) (by norm_num)
theorem B18175445 : Blo 698317 18175445 := bbase (se 7 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 18175445 = 425987) (by norm_num)
theorem B2840021 : Blo 698317 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B1332749 : Blo 698317 1332749 := bbase (se 3 (by rfl) ⟨249890, by rfl⟩ : syracuseStep 1332749 = 499781) (by norm_num)
theorem B3593909 : Blo 698317 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B1496789 : Blo 698317 1496789 := bbase (se 7 (by rfl) ⟨17540, by rfl⟩ : syracuseStep 1496789 = 35081) (by norm_num)
theorem B1333037 : Blo 698317 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B1333189 : Blo 698317 1333189 := bbase (se 4 (by rfl) ⟨124986, by rfl⟩ : syracuseStep 1333189 = 249973) (by norm_num)
theorem B5330933 : Blo 698317 5330933 := bbase (se 5 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 5330933 = 499775) (by norm_num)
theorem B1824925 : Blo 698317 1824925 := bbase (se 3 (by rfl) ⟨342173, by rfl⟩ : syracuseStep 1824925 = 684347) (by norm_num)
theorem B5986709 : Blo 698317 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B1497541 : Blo 698317 1497541 := bbase (se 4 (by rfl) ⟨140394, by rfl⟩ : syracuseStep 1497541 = 280789) (by norm_num)
theorem B3365333 : Blo 698317 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B1366541 : Blo 698317 1366541 := bbase (se 3 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 1366541 = 512453) (by norm_num)
theorem B1989157 : Blo 698317 1989157 := bbase (se 4 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 1989157 = 372967) (by norm_num)
theorem B3201589 : Blo 698317 3201589 := bbase (se 5 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 3201589 = 300149) (by norm_num)
theorem B1497685 : Blo 698317 1497685 := bbase (se 8 (by rfl) ⟨8775, by rfl⟩ : syracuseStep 1497685 = 17551) (by norm_num)
theorem B842405 : Blo 698317 842405 := bbase (se 4 (by rfl) ⟨78975, by rfl⟩ : syracuseStep 842405 = 157951) (by norm_num)
theorem B1596125 : Blo 698317 1596125 := bbase (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) (by norm_num)
theorem B1498061 : Blo 698317 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B842737 : Blo 698317 842737 := bbase (se 2 (by rfl) ⟨316026, by rfl⟩ : syracuseStep 842737 = 632053) (by norm_num)
theorem B842881 : Blo 698317 842881 := bbase (se 2 (by rfl) ⟨316080, by rfl⟩ : syracuseStep 842881 = 632161) (by norm_num)
theorem B3792053 : Blo 698317 3792053 := bbase (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) (by norm_num)
theorem B1498429 : Blo 698317 1498429 := bbase (se 3 (by rfl) ⟨280955, by rfl⟩ : syracuseStep 1498429 = 561911) (by norm_num)
theorem B810389 : Blo 698317 810389 := bbase (se 6 (by rfl) ⟨18993, by rfl⟩ : syracuseStep 810389 = 37987) (by norm_num)
theorem B1990261 : Blo 698317 1990261 := bbase (se 5 (by rfl) ⟨93293, by rfl⟩ : syracuseStep 1990261 = 186587) (by norm_num)
theorem B1793669 : Blo 698317 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B1793773 : Blo 698317 1793773 := bbase (se 3 (by rfl) ⟨336332, by rfl⟩ : syracuseStep 1793773 = 672665) (by norm_num)
theorem B909041 : Blo 698317 909041 := bbase (se 2 (by rfl) ⟨340890, by rfl⟩ : syracuseStep 909041 = 681781) (by norm_num)
theorem B1793917 : Blo 698317 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B811217 : Blo 698317 811217 := bbase (se 2 (by rfl) ⟨304206, by rfl⟩ : syracuseStep 811217 = 608413) (by norm_num)
theorem B745733 : Blo 698317 745733 := bbase (se 4 (by rfl) ⟨69912, by rfl⟩ : syracuseStep 745733 = 139825) (by norm_num)
theorem B3203525 : Blo 698317 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B811577 : Blo 698317 811577 := bbase (se 2 (by rfl) ⟨304341, by rfl⟩ : syracuseStep 811577 = 608683) (by norm_num)
theorem B811661 : Blo 698317 811661 := bbase (se 3 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 811661 = 304373) (by norm_num)
theorem B746177 : Blo 698317 746177 := bbase (se 2 (by rfl) ⟨279816, by rfl⟩ : syracuseStep 746177 = 559633) (by norm_num)
theorem B1499933 : Blo 698317 1499933 := bbase (se 3 (by rfl) ⟨281237, by rfl⟩ : syracuseStep 1499933 = 562475) (by norm_num)
theorem B1794901 : Blo 698317 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B746425 : Blo 698317 746425 := bbase (se 2 (by rfl) ⟨279909, by rfl⟩ : syracuseStep 746425 = 559819) (by norm_num)
theorem B1369037 : Blo 698317 1369037 := bbase (se 3 (by rfl) ⟨256694, by rfl⟩ : syracuseStep 1369037 = 513389) (by norm_num)
theorem B1991765 : Blo 698317 1991765 := bbase (se 8 (by rfl) ⟨11670, by rfl⟩ : syracuseStep 1991765 = 23341) (by norm_num)
theorem B3368101 : Blo 698317 3368101 := bbase (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) (by norm_num)
theorem B1598717 : Blo 698317 1598717 := bbase (se 3 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 1598717 = 599519) (by norm_num)
theorem B746857 : Blo 698317 746857 := bbase (se 2 (by rfl) ⟨280071, by rfl⟩ : syracuseStep 746857 = 560143) (by norm_num)
theorem B746929 : Blo 698317 746929 := bbase (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) (by norm_num)
theorem B1533421 : Blo 698317 1533421 := bbase (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) (by norm_num)
theorem B779825 : Blo 698317 779825 := bbase (se 2 (by rfl) ⟨292434, by rfl⟩ : syracuseStep 779825 = 584869) (by norm_num)
theorem B747301 : Blo 698317 747301 := bbase (se 4 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 747301 = 140119) (by norm_num)
theorem B2844821 : Blo 698317 2844821 := bbase (se 6 (by rfl) ⟨66675, by rfl⟩ : syracuseStep 2844821 = 133351) (by norm_num)
theorem B747677 : Blo 698317 747677 := bbase (se 3 (by rfl) ⟨140189, by rfl⟩ : syracuseStep 747677 = 280379) (by norm_num)
theorem B747749 : Blo 698317 747749 := bbase (se 4 (by rfl) ⟨70101, by rfl⟩ : syracuseStep 747749 = 140203) (by norm_num)
theorem B747937 : Blo 698317 747937 := bbase (se 2 (by rfl) ⟨280476, by rfl⟩ : syracuseStep 747937 = 560953) (by norm_num)
theorem B748121 : Blo 698317 748121 := bbase (se 2 (by rfl) ⟨280545, by rfl⟩ : syracuseStep 748121 = 561091) (by norm_num)
theorem B1796701 : Blo 698317 1796701 := bbase (se 3 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 1796701 = 673763) (by norm_num)
theorem B1993349 : Blo 698317 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B6056693 : Blo 698317 6056693 := bbase (se 5 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 6056693 = 567815) (by norm_num)
theorem B4483829 : Blo 698317 4483829 := bbase (se 5 (by rfl) ⟨210179, by rfl⟩ : syracuseStep 4483829 = 420359) (by norm_num)
theorem B1600469 : Blo 698317 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B3992597 : Blo 698317 3992597 := bbase (se 6 (by rfl) ⟨93576, by rfl⟩ : syracuseStep 3992597 = 187153) (by norm_num)
theorem B2845925 : Blo 698317 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B1994021 : Blo 698317 1994021 := bbase (se 4 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 1994021 = 373879) (by norm_num)
theorem B748873 : Blo 698317 748873 := bbase (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) (by norm_num)
theorem B748945 : Blo 698317 748945 := bbase (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) (by norm_num)
theorem B2846117 : Blo 698317 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B749125 : Blo 698317 749125 := bbase (se 4 (by rfl) ⟨70230, by rfl⟩ : syracuseStep 749125 = 140461) (by norm_num)
theorem B1994453 : Blo 698317 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B7302869 : Blo 698317 7302869 := bbase (se 7 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 7302869 = 171161) (by norm_num)
theorem B1896373 : Blo 698317 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B1601525 : Blo 698317 1601525 := bbase (se 5 (by rfl) ⟨75071, by rfl⟩ : syracuseStep 1601525 = 150143) (by norm_num)
theorem B749569 : Blo 698317 749569 := bbase (se 2 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 749569 = 562177) (by norm_num)
theorem B749693 : Blo 698317 749693 := bbase (se 3 (by rfl) ⟨140567, by rfl⟩ : syracuseStep 749693 = 281135) (by norm_num)
theorem B5402933 : Blo 698317 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B749945 : Blo 698317 749945 := bbase (se 2 (by rfl) ⟨281229, by rfl⟩ : syracuseStep 749945 = 562459) (by norm_num)
theorem B1995205 : Blo 698317 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B2126341 : Blo 698317 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B1798669 : Blo 698317 1798669 := bbase (se 3 (by rfl) ⟨337250, by rfl⟩ : syracuseStep 1798669 = 674501) (by norm_num)
theorem B2847269 : Blo 698317 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B3600949 : Blo 698317 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B1700869 : Blo 698317 1700869 := bbase (se 4 (by rfl) ⟨159456, by rfl⟩ : syracuseStep 1700869 = 318913) (by norm_num)
theorem B3535973 : Blo 698317 3535973 := bbase (se 4 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 3535973 = 662995) (by norm_num)
theorem B1537165 : Blo 698317 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B3372293 : Blo 698317 3372293 := bbase (se 4 (by rfl) ⟨316152, by rfl⟩ : syracuseStep 3372293 = 632305) (by norm_num)
theorem B2520341 : Blo 698317 2520341 := bbase (se 6 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 2520341 = 118141) (by norm_num)
theorem B947581 : Blo 698317 947581 := bbase (se 3 (by rfl) ⟨177671, by rfl⟩ : syracuseStep 947581 = 355343) (by norm_num)
theorem B2651525 : Blo 698317 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B6715061 : Blo 698317 6715061 := bbase (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) (by norm_num)
theorem B2520757 : Blo 698317 2520757 := bbase (se 5 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 2520757 = 236321) (by norm_num)
theorem B2357045 : Blo 698317 2357045 := bbase (se 5 (by rfl) ⟨110486, by rfl⟩ : syracuseStep 2357045 = 220973) (by norm_num)
theorem B3405797 : Blo 698317 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B1767653 : Blo 698317 1767653 := bbase (se 4 (by rfl) ⟨165717, by rfl⟩ : syracuseStep 1767653 = 331435) (by norm_num)
theorem B2357477 : Blo 698317 2357477 := bbase (se 4 (by rfl) ⟨221013, by rfl⟩ : syracuseStep 2357477 = 442027) (by norm_num)
theorem B3537269 : Blo 698317 3537269 := bbase (se 5 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 3537269 = 331619) (by norm_num)
theorem B2521493 : Blo 698317 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B1571237 : Blo 698317 1571237 := bbase (se 4 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 1571237 = 294607) (by norm_num)
theorem B1767845 : Blo 698317 1767845 := bbase (se 4 (by rfl) ⟨165735, by rfl⟩ : syracuseStep 1767845 = 331471) (by norm_num)
theorem B1571309 : Blo 698317 1571309 := bbase (se 3 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 1571309 = 589241) (by norm_num)
theorem B2652709 : Blo 698317 2652709 := bbase (se 4 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 2652709 = 497383) (by norm_num)
theorem B1571381 : Blo 698317 1571381 := bbase (se 5 (by rfl) ⟨73658, by rfl⟩ : syracuseStep 1571381 = 147317) (by norm_num)
theorem B1571453 : Blo 698317 1571453 := bbase (se 3 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 1571453 = 589295) (by norm_num)
theorem B2357909 : Blo 698317 2357909 := bbase (se 6 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 2357909 = 110527) (by norm_num)
theorem B12974741 : Blo 698317 12974741 := bbase (se 6 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 12974741 = 608191) (by norm_num)
theorem B1571525 : Blo 698317 1571525 := bbase (se 4 (by rfl) ⟨147330, by rfl⟩ : syracuseStep 1571525 = 294661) (by norm_num)
theorem B1768189 : Blo 698317 1768189 := bbase (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) (by norm_num)
theorem B1571597 : Blo 698317 1571597 := bbase (se 3 (by rfl) ⟨294674, by rfl⟩ : syracuseStep 1571597 = 589349) (by norm_num)
theorem B4782901 : Blo 698317 4782901 := bbase (se 5 (by rfl) ⟨224198, by rfl⟩ : syracuseStep 4782901 = 448397) (by norm_num)
theorem B1571669 : Blo 698317 1571669 := bbase (se 9 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 1571669 = 9209) (by norm_num)
theorem B2653013 : Blo 698317 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B1768301 : Blo 698317 1768301 := bbase (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) (by norm_num)
theorem B1178509 : Blo 698317 1178509 := bbase (se 3 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 1178509 = 441941) (by norm_num)
theorem B1571741 : Blo 698317 1571741 := bbase (se 3 (by rfl) ⟨294701, by rfl⟩ : syracuseStep 1571741 = 589403) (by norm_num)
theorem B1047485 : Blo 698317 1047485 := bbase (se 3 (by rfl) ⟨196403, by rfl⟩ : syracuseStep 1047485 = 392807) (by norm_num)
theorem B1047509 : Blo 698317 1047509 := bbase (se 7 (by rfl) ⟨12275, by rfl⟩ : syracuseStep 1047509 = 24551) (by norm_num)
theorem B1178597 : Blo 698317 1178597 := bbase (se 4 (by rfl) ⟨110493, by rfl⟩ : syracuseStep 1178597 = 220987) (by norm_num)
theorem B1571813 : Blo 698317 1571813 := bbase (se 4 (by rfl) ⟨147357, by rfl⟩ : syracuseStep 1571813 = 294715) (by norm_num)
theorem B1047533 : Blo 698317 1047533 := bbase (se 3 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 1047533 = 392825) (by norm_num)
theorem B1047557 : Blo 698317 1047557 := bbase (se 4 (by rfl) ⟨98208, by rfl⟩ : syracuseStep 1047557 = 196417) (by norm_num)
theorem B1047581 : Blo 698317 1047581 := bbase (se 3 (by rfl) ⟨196421, by rfl⟩ : syracuseStep 1047581 = 392843) (by norm_num)
theorem B1571885 : Blo 698317 1571885 := bbase (se 3 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 1571885 = 589457) (by norm_num)
theorem B1768493 : Blo 698317 1768493 := bbase (se 3 (by rfl) ⟨331592, by rfl⟩ : syracuseStep 1768493 = 663185) (by norm_num)
theorem B1047605 : Blo 698317 1047605 := bbase (se 5 (by rfl) ⟨49106, by rfl⟩ : syracuseStep 1047605 = 98213) (by norm_num)
theorem B2358341 : Blo 698317 2358341 := bbase (se 4 (by rfl) ⟨221094, by rfl⟩ : syracuseStep 2358341 = 442189) (by norm_num)
theorem B1047629 : Blo 698317 1047629 := bbase (se 3 (by rfl) ⟨196430, by rfl⟩ : syracuseStep 1047629 = 392861) (by norm_num)
theorem B1047653 : Blo 698317 1047653 := bbase (se 4 (by rfl) ⟨98217, by rfl⟩ : syracuseStep 1047653 = 196435) (by norm_num)
theorem B1178725 : Blo 698317 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B1571957 : Blo 698317 1571957 := bbase (se 5 (by rfl) ⟨73685, by rfl⟩ : syracuseStep 1571957 = 147371) (by norm_num)
theorem B1047677 : Blo 698317 1047677 := bbase (se 3 (by rfl) ⟨196439, by rfl⟩ : syracuseStep 1047677 = 392879) (by norm_num)
theorem B1047701 : Blo 698317 1047701 := bbase (se 6 (by rfl) ⟨24555, by rfl⟩ : syracuseStep 1047701 = 49111) (by norm_num)
theorem B1047725 : Blo 698317 1047725 := bbase (se 3 (by rfl) ⟨196448, by rfl⟩ : syracuseStep 1047725 = 392897) (by norm_num)
theorem B1178813 : Blo 698317 1178813 := bbase (se 3 (by rfl) ⟨221027, by rfl⟩ : syracuseStep 1178813 = 442055) (by norm_num)
theorem B1572029 : Blo 698317 1572029 := bbase (se 3 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 1572029 = 589511) (by norm_num)
theorem B1047749 : Blo 698317 1047749 := bbase (se 4 (by rfl) ⟨98226, by rfl⟩ : syracuseStep 1047749 = 196453) (by norm_num)
theorem B5307605 : Blo 698317 5307605 := bbase (se 7 (by rfl) ⟨62198, by rfl⟩ : syracuseStep 5307605 = 124397) (by norm_num)
theorem B1047773 : Blo 698317 1047773 := bbase (se 3 (by rfl) ⟨196457, by rfl⟩ : syracuseStep 1047773 = 392915) (by norm_num)
theorem B1998053 : Blo 698317 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B785641 : Blo 698317 785641 := bbase (se 2 (by rfl) ⟨294615, by rfl⟩ : syracuseStep 785641 = 589231) (by norm_num)
theorem B1047797 : Blo 698317 1047797 := bbase (se 5 (by rfl) ⟨49115, by rfl⟩ : syracuseStep 1047797 = 98231) (by norm_num)
theorem B883973 : Blo 698317 883973 := bbase (se 4 (by rfl) ⟨82872, by rfl⟩ : syracuseStep 883973 = 165745) (by norm_num)
theorem B1572101 : Blo 698317 1572101 := bbase (se 4 (by rfl) ⟨147384, by rfl⟩ : syracuseStep 1572101 = 294769) (by norm_num)
theorem B785677 : Blo 698317 785677 := bbase (se 3 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 785677 = 294629) (by norm_num)
theorem B1047821 : Blo 698317 1047821 := bbase (se 3 (by rfl) ⟨196466, by rfl⟩ : syracuseStep 1047821 = 392933) (by norm_num)
theorem B1047845 : Blo 698317 1047845 := bbase (se 4 (by rfl) ⟨98235, by rfl⟩ : syracuseStep 1047845 = 196471) (by norm_num)
theorem B785713 : Blo 698317 785713 := bbase (se 2 (by rfl) ⟨294642, by rfl⟩ : syracuseStep 785713 = 589285) (by norm_num)
theorem B884029 : Blo 698317 884029 := bbase (se 3 (by rfl) ⟨165755, by rfl⟩ : syracuseStep 884029 = 331511) (by norm_num)
theorem B1047869 : Blo 698317 1047869 := bbase (se 3 (by rfl) ⟨196475, by rfl⟩ : syracuseStep 1047869 = 392951) (by norm_num)
theorem B1178941 : Blo 698317 1178941 := bbase (se 3 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 1178941 = 442103) (by norm_num)
theorem B1572173 : Blo 698317 1572173 := bbase (se 3 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 1572173 = 589565) (by norm_num)
theorem B785749 : Blo 698317 785749 := bbase (se 11 (by rfl) ⟨575, by rfl⟩ : syracuseStep 785749 = 1151) (by norm_num)
theorem B1047893 : Blo 698317 1047893 := bbase (se 11 (by rfl) ⟨767, by rfl⟩ : syracuseStep 1047893 = 1535) (by norm_num)
theorem B1047917 : Blo 698317 1047917 := bbase (se 3 (by rfl) ⟨196484, by rfl⟩ : syracuseStep 1047917 = 392969) (by norm_num)
theorem B785785 : Blo 698317 785785 := bbase (se 2 (by rfl) ⟨294669, by rfl⟩ : syracuseStep 785785 = 589339) (by norm_num)
theorem B1047941 : Blo 698317 1047941 := bbase (se 4 (by rfl) ⟨98244, by rfl⟩ : syracuseStep 1047941 = 196489) (by norm_num)
theorem B1768837 : Blo 698317 1768837 := bbase (se 4 (by rfl) ⟨165828, by rfl⟩ : syracuseStep 1768837 = 331657) (by norm_num)
theorem B1179029 : Blo 698317 1179029 := bbase (se 6 (by rfl) ⟨27633, by rfl⟩ : syracuseStep 1179029 = 55267) (by norm_num)
theorem B1572245 : Blo 698317 1572245 := bbase (se 6 (by rfl) ⟨36849, by rfl⟩ : syracuseStep 1572245 = 73699) (by norm_num)
theorem B785821 : Blo 698317 785821 := bbase (se 3 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 785821 = 294683) (by norm_num)
theorem B884125 : Blo 698317 884125 := bbase (se 3 (by rfl) ⟨165773, by rfl⟩ : syracuseStep 884125 = 331547) (by norm_num)
theorem B1047965 : Blo 698317 1047965 := bbase (se 3 (by rfl) ⟨196493, by rfl⟩ : syracuseStep 1047965 = 392987) (by norm_num)
theorem B1047989 : Blo 698317 1047989 := bbase (se 5 (by rfl) ⟨49124, by rfl⟩ : syracuseStep 1047989 = 98249) (by norm_num)
theorem B785857 : Blo 698317 785857 := bbase (se 2 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 785857 = 589393) (by norm_num)
theorem B1048013 : Blo 698317 1048013 := bbase (se 3 (by rfl) ⟨196502, by rfl⟩ : syracuseStep 1048013 = 393005) (by norm_num)
theorem B1572317 : Blo 698317 1572317 := bbase (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) (by norm_num)
theorem B785893 : Blo 698317 785893 := bbase (se 4 (by rfl) ⟨73677, by rfl⟩ : syracuseStep 785893 = 147355) (by norm_num)
theorem B1048037 : Blo 698317 1048037 := bbase (se 4 (by rfl) ⟨98253, by rfl⟩ : syracuseStep 1048037 = 196507) (by norm_num)
theorem B1768949 : Blo 698317 1768949 := bbase (se 5 (by rfl) ⟨82919, by rfl⟩ : syracuseStep 1768949 = 165839) (by norm_num)
theorem B2358773 : Blo 698317 2358773 := bbase (se 5 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 2358773 = 221135) (by norm_num)
theorem B1048061 : Blo 698317 1048061 := bbase (se 3 (by rfl) ⟨196511, by rfl⟩ : syracuseStep 1048061 = 393023) (by norm_num)
theorem B785929 : Blo 698317 785929 := bbase (se 2 (by rfl) ⟨294723, by rfl⟩ : syracuseStep 785929 = 589447) (by norm_num)
theorem B1048085 : Blo 698317 1048085 := bbase (se 6 (by rfl) ⟨24564, by rfl⟩ : syracuseStep 1048085 = 49129) (by norm_num)
theorem B1179157 : Blo 698317 1179157 := bbase (se 6 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 1179157 = 55273) (by norm_num)
theorem B1572389 : Blo 698317 1572389 := bbase (se 4 (by rfl) ⟨147411, by rfl⟩ : syracuseStep 1572389 = 294823) (by norm_num)
theorem B785965 : Blo 698317 785965 := bbase (se 3 (by rfl) ⟨147368, by rfl⟩ : syracuseStep 785965 = 294737) (by norm_num)
theorem B1048109 : Blo 698317 1048109 := bbase (se 3 (by rfl) ⟨196520, by rfl⟩ : syracuseStep 1048109 = 393041) (by norm_num)
theorem B1048133 : Blo 698317 1048133 := bbase (se 4 (by rfl) ⟨98262, by rfl⟩ : syracuseStep 1048133 = 196525) (by norm_num)
theorem B884297 : Blo 698317 884297 := bbase (se 2 (by rfl) ⟨331611, by rfl⟩ : syracuseStep 884297 = 663223) (by norm_num)
theorem B786001 : Blo 698317 786001 := bbase (se 2 (by rfl) ⟨294750, by rfl⟩ : syracuseStep 786001 = 589501) (by norm_num)
theorem B1048157 : Blo 698317 1048157 := bbase (se 3 (by rfl) ⟨196529, by rfl⟩ : syracuseStep 1048157 = 393059) (by norm_num)
theorem B1179245 : Blo 698317 1179245 := bbase (se 3 (by rfl) ⟨221108, by rfl⟩ : syracuseStep 1179245 = 442217) (by norm_num)
theorem B1572461 : Blo 698317 1572461 := bbase (se 3 (by rfl) ⟨294836, by rfl⟩ : syracuseStep 1572461 = 589673) (by norm_num)
theorem B786037 : Blo 698317 786037 := bbase (se 5 (by rfl) ⟨36845, by rfl⟩ : syracuseStep 786037 = 73691) (by norm_num)
theorem B1048181 : Blo 698317 1048181 := bbase (se 5 (by rfl) ⟨49133, by rfl⟩ : syracuseStep 1048181 = 98267) (by norm_num)
theorem B884353 : Blo 698317 884353 := bbase (se 2 (by rfl) ⟨331632, by rfl⟩ : syracuseStep 884353 = 663265) (by norm_num)
theorem B3538565 : Blo 698317 3538565 := bbase (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) (by norm_num)
theorem B1048205 : Blo 698317 1048205 := bbase (se 3 (by rfl) ⟨196538, by rfl⟩ : syracuseStep 1048205 = 393077) (by norm_num)
theorem B786073 : Blo 698317 786073 := bbase (se 2 (by rfl) ⟨294777, by rfl⟩ : syracuseStep 786073 = 589555) (by norm_num)
theorem B1048229 : Blo 698317 1048229 := bbase (se 4 (by rfl) ⟨98271, by rfl⟩ : syracuseStep 1048229 = 196543) (by norm_num)
theorem B1572533 : Blo 698317 1572533 := bbase (se 5 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 1572533 = 147425) (by norm_num)
theorem B1769141 : Blo 698317 1769141 := bbase (se 5 (by rfl) ⟨82928, by rfl⟩ : syracuseStep 1769141 = 165857) (by norm_num)
theorem B786109 : Blo 698317 786109 := bbase (se 3 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 786109 = 294791) (by norm_num)
theorem B1048253 : Blo 698317 1048253 := bbase (se 3 (by rfl) ⟨196547, by rfl⟩ : syracuseStep 1048253 = 393095) (by norm_num)
theorem B1048277 : Blo 698317 1048277 := bbase (se 7 (by rfl) ⟨12284, by rfl⟩ : syracuseStep 1048277 = 24569) (by norm_num)
theorem B786145 : Blo 698317 786145 := bbase (se 2 (by rfl) ⟨294804, by rfl⟩ : syracuseStep 786145 = 589609) (by norm_num)
theorem B884449 : Blo 698317 884449 := bbase (se 2 (by rfl) ⟨331668, by rfl⟩ : syracuseStep 884449 = 663337) (by norm_num)
theorem B1048301 : Blo 698317 1048301 := bbase (se 3 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 1048301 = 393113) (by norm_num)
theorem B1179373 : Blo 698317 1179373 := bbase (se 3 (by rfl) ⟨221132, by rfl⟩ : syracuseStep 1179373 = 442265) (by norm_num)
theorem B1572605 : Blo 698317 1572605 := bbase (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) (by norm_num)
theorem B786181 : Blo 698317 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B1048325 : Blo 698317 1048325 := bbase (se 4 (by rfl) ⟨98280, by rfl⟩ : syracuseStep 1048325 = 196561) (by norm_num)
theorem B1048349 : Blo 698317 1048349 := bbase (se 3 (by rfl) ⟨196565, by rfl⟩ : syracuseStep 1048349 = 393131) (by norm_num)
theorem B786217 : Blo 698317 786217 := bbase (se 2 (by rfl) ⟨294831, by rfl⟩ : syracuseStep 786217 = 589663) (by norm_num)
theorem B1048373 : Blo 698317 1048373 := bbase (se 5 (by rfl) ⟨49142, by rfl⟩ : syracuseStep 1048373 = 98285) (by norm_num)
theorem B1179461 : Blo 698317 1179461 := bbase (se 4 (by rfl) ⟨110574, by rfl⟩ : syracuseStep 1179461 = 221149) (by norm_num)
theorem B1572677 : Blo 698317 1572677 := bbase (se 4 (by rfl) ⟨147438, by rfl⟩ : syracuseStep 1572677 = 294877) (by norm_num)
theorem B786253 : Blo 698317 786253 := bbase (se 3 (by rfl) ⟨147422, by rfl⟩ : syracuseStep 786253 = 294845) (by norm_num)
theorem B1048397 : Blo 698317 1048397 := bbase (se 3 (by rfl) ⟨196574, by rfl⟩ : syracuseStep 1048397 = 393149) (by norm_num)
theorem B851809 : Blo 698317 851809 := bbase (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) (by norm_num)
theorem B1048421 : Blo 698317 1048421 := bbase (se 4 (by rfl) ⟨98289, by rfl⟩ : syracuseStep 1048421 = 196579) (by norm_num)
theorem B786289 : Blo 698317 786289 := bbase (se 2 (by rfl) ⟨294858, by rfl⟩ : syracuseStep 786289 = 589717) (by norm_num)
theorem B1048445 : Blo 698317 1048445 := bbase (se 3 (by rfl) ⟨196583, by rfl⟩ : syracuseStep 1048445 = 393167) (by norm_num)
theorem B884621 : Blo 698317 884621 := bbase (se 3 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 884621 = 331733) (by norm_num)
theorem B1572749 : Blo 698317 1572749 := bbase (se 3 (by rfl) ⟨294890, by rfl⟩ : syracuseStep 1572749 = 589781) (by norm_num)
theorem B786325 : Blo 698317 786325 := bbase (se 6 (by rfl) ⟨18429, by rfl⟩ : syracuseStep 786325 = 36859) (by norm_num)
theorem B1048469 : Blo 698317 1048469 := bbase (se 6 (by rfl) ⟨24573, by rfl⟩ : syracuseStep 1048469 = 49147) (by norm_num)
theorem B2359205 : Blo 698317 2359205 := bbase (se 4 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 2359205 = 442351) (by norm_num)
theorem B1048493 : Blo 698317 1048493 := bbase (se 3 (by rfl) ⟨196592, by rfl⟩ : syracuseStep 1048493 = 393185) (by norm_num)
theorem B786361 : Blo 698317 786361 := bbase (se 2 (by rfl) ⟨294885, by rfl⟩ : syracuseStep 786361 = 589771) (by norm_num)
theorem B884677 : Blo 698317 884677 := bbase (se 4 (by rfl) ⟨82938, by rfl⟩ : syracuseStep 884677 = 165877) (by norm_num)
theorem B1048517 : Blo 698317 1048517 := bbase (se 4 (by rfl) ⟨98298, by rfl⟩ : syracuseStep 1048517 = 196597) (by norm_num)
theorem B1179589 : Blo 698317 1179589 := bbase (se 4 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 1179589 = 221173) (by norm_num)
theorem B2523077 : Blo 698317 2523077 := bbase (se 4 (by rfl) ⟨236538, by rfl⟩ : syracuseStep 2523077 = 473077) (by norm_num)
theorem B1572821 : Blo 698317 1572821 := bbase (se 7 (by rfl) ⟨18431, by rfl⟩ : syracuseStep 1572821 = 36863) (by norm_num)
theorem B786397 : Blo 698317 786397 := bbase (se 3 (by rfl) ⟨147449, by rfl⟩ : syracuseStep 786397 = 294899) (by norm_num)
theorem B1048541 : Blo 698317 1048541 := bbase (se 3 (by rfl) ⟨196601, by rfl⟩ : syracuseStep 1048541 = 393203) (by norm_num)
theorem B1048565 : Blo 698317 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B1048577 : Blo 698317 1048577 := bstep (se 2 (by rfl) ⟨393216, by rfl⟩ : syracuseStep 1048577 = 786433) B786433
theorem B2359313 : Blo 698317 2359313 := bstep (se 2 (by rfl) ⟨884742, by rfl⟩ : syracuseStep 2359313 = 1769485) B1769485
theorem B1048595 : Blo 698317 1048595 := bstep (se 1 (by rfl) ⟨786446, by rfl⟩ : syracuseStep 1048595 = 1572893) B1572893
theorem B786451 : Blo 698317 786451 := bstep (se 1 (by rfl) ⟨589838, by rfl⟩ : syracuseStep 786451 = 1179677) B1179677
theorem B1179697 : Blo 698317 1179697 := bstep (se 2 (by rfl) ⟨442386, by rfl⟩ : syracuseStep 1179697 = 884773) B884773
theorem B1048625 : Blo 698317 1048625 := bstep (se 2 (by rfl) ⟨393234, by rfl⟩ : syracuseStep 1048625 = 786469) B786469
theorem B3997745 : Blo 698317 3997745 := bstep (se 2 (by rfl) ⟨1499154, by rfl⟩ : syracuseStep 3997745 = 2998309) B2998309
theorem B1048643 : Blo 698317 1048643 := bstep (se 1 (by rfl) ⟨786482, by rfl⟩ : syracuseStep 1048643 = 1572965) B1572965
theorem B1179731 : Blo 698317 1179731 := bstep (se 1 (by rfl) ⟨884798, by rfl⟩ : syracuseStep 1179731 = 1769597) B1769597
theorem B1048673 : Blo 698317 1048673 := bstep (se 2 (by rfl) ⟨393252, by rfl⟩ : syracuseStep 1048673 = 786505) B786505
theorem B1048691 : Blo 698317 1048691 := bstep (se 1 (by rfl) ⟨786518, by rfl⟩ : syracuseStep 1048691 = 1573037) B1573037
theorem B1048721 : Blo 698317 1048721 := bstep (se 2 (by rfl) ⟨393270, by rfl⟩ : syracuseStep 1048721 = 786541) B786541
theorem B1048739 : Blo 698317 1048739 := bstep (se 1 (by rfl) ⟨786554, by rfl⟩ : syracuseStep 1048739 = 1573109) B1573109
theorem B786595 : Blo 698317 786595 := bstep (se 1 (by rfl) ⟨589946, by rfl⟩ : syracuseStep 786595 = 1179893) B1179893
theorem B1048769 : Blo 698317 1048769 := bstep (se 2 (by rfl) ⟨393288, by rfl⟩ : syracuseStep 1048769 = 786577) B786577
theorem B1573073 : Blo 698317 1573073 := bstep (se 2 (by rfl) ⟨589902, by rfl⟩ : syracuseStep 1573073 = 1179805) B1179805
theorem B1179859 : Blo 698317 1179859 := bstep (se 1 (by rfl) ⟨884894, by rfl⟩ : syracuseStep 1179859 = 1769789) B1769789
theorem B1048787 : Blo 698317 1048787 := bstep (se 1 (by rfl) ⟨786590, by rfl⟩ : syracuseStep 1048787 = 1573181) B1573181
theorem B1573091 : Blo 698317 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B1048817 : Blo 698317 1048817 := bstep (se 2 (by rfl) ⟨393306, by rfl⟩ : syracuseStep 1048817 = 786613) B786613
theorem B1048835 : Blo 698317 1048835 := bstep (se 1 (by rfl) ⟨786626, by rfl⟩ : syracuseStep 1048835 = 1573253) B1573253
theorem B3539213 : Blo 698317 3539213 := bstep (se 3 (by rfl) ⟨663602, by rfl⟩ : syracuseStep 3539213 = 1327205) B1327205
theorem B1048865 : Blo 698317 1048865 := bstep (se 2 (by rfl) ⟨393324, by rfl⟩ : syracuseStep 1048865 = 786649) B786649
theorem B1048883 : Blo 698317 1048883 := bstep (se 1 (by rfl) ⟨786662, by rfl⟩ : syracuseStep 1048883 = 1573325) B1573325
theorem B786739 : Blo 698317 786739 := bstep (se 1 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 786739 = 1180109) B1180109
theorem B1999181 : Blo 698317 1999181 := bstep (se 3 (by rfl) ⟨374846, by rfl⟩ : syracuseStep 1999181 = 749693) B749693
theorem B1769809 : Blo 698317 1769809 := bstep (se 2 (by rfl) ⟨663678, by rfl⟩ : syracuseStep 1769809 = 1327357) B1327357
theorem B1048913 : Blo 698317 1048913 := bstep (se 2 (by rfl) ⟨393342, by rfl⟩ : syracuseStep 1048913 = 786685) B786685
theorem B1180001 : Blo 698317 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B1048931 : Blo 698317 1048931 := bstep (se 1 (by rfl) ⟨786698, by rfl⟩ : syracuseStep 1048931 = 1573397) B1573397
theorem B885107 : Blo 698317 885107 := bstep (se 1 (by rfl) ⟨663830, by rfl⟩ : syracuseStep 885107 = 1327661) B1327661
theorem B1048961 : Blo 698317 1048961 := bstep (se 2 (by rfl) ⟨393360, by rfl⟩ : syracuseStep 1048961 = 786721) B786721
theorem B1048979 : Blo 698317 1048979 := bstep (se 1 (by rfl) ⟨786734, by rfl⟩ : syracuseStep 1048979 = 1573469) B1573469
theorem B1049009 : Blo 698317 1049009 := bstep (se 2 (by rfl) ⟨393378, by rfl⟩ : syracuseStep 1049009 = 786757) B786757
theorem B1049027 : Blo 698317 1049027 := bstep (se 1 (by rfl) ⟨786770, by rfl⟩ : syracuseStep 1049027 = 1573541) B1573541
theorem B786883 : Blo 698317 786883 := bstep (se 1 (by rfl) ⟨590162, by rfl⟩ : syracuseStep 786883 = 1180325) B1180325
theorem B1180129 : Blo 698317 1180129 := bstep (se 2 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 1180129 = 885097) B885097
theorem B1049057 : Blo 698317 1049057 := bstep (se 2 (by rfl) ⟨393396, by rfl⟩ : syracuseStep 1049057 = 786793) B786793
theorem B1573361 : Blo 698317 1573361 := bstep (se 2 (by rfl) ⟨590010, by rfl⟩ : syracuseStep 1573361 = 1180021) B1180021
theorem B1049075 : Blo 698317 1049075 := bstep (se 1 (by rfl) ⟨786806, by rfl⟩ : syracuseStep 1049075 = 1573613) B1573613
theorem B1573379 : Blo 698317 1573379 := bstep (se 1 (by rfl) ⟨1180034, by rfl⟩ : syracuseStep 1573379 = 2360069) B2360069
theorem B1180163 : Blo 698317 1180163 := bstep (se 1 (by rfl) ⟨885122, by rfl⟩ : syracuseStep 1180163 = 1770245) B1770245
theorem B1999363 : Blo 698317 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B1049105 : Blo 698317 1049105 := bstep (se 2 (by rfl) ⟨393414, by rfl⟩ : syracuseStep 1049105 = 786829) B786829
theorem B1049123 : Blo 698317 1049123 := bstep (se 1 (by rfl) ⟨786842, by rfl⟩ : syracuseStep 1049123 = 1573685) B1573685
theorem B2359853 : Blo 698317 2359853 := bstep (se 3 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 2359853 = 884945) B884945
theorem B2163245 : Blo 698317 2163245 := bstep (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) B811217
theorem B1049153 : Blo 698317 1049153 := bstep (se 2 (by rfl) ⟨393432, by rfl⟩ : syracuseStep 1049153 = 786865) B786865
theorem B1049171 : Blo 698317 1049171 := bstep (se 1 (by rfl) ⟨786878, by rfl⟩ : syracuseStep 1049171 = 1573757) B1573757
theorem B787027 : Blo 698317 787027 := bstep (se 1 (by rfl) ⟨590270, by rfl⟩ : syracuseStep 787027 = 1180541) B1180541
theorem B2359907 : Blo 698317 2359907 := bstep (se 1 (by rfl) ⟨1769930, by rfl⟩ : syracuseStep 2359907 = 3539861) B3539861
theorem B1770083 : Blo 698317 1770083 := bstep (se 1 (by rfl) ⟨1327562, by rfl⟩ : syracuseStep 1770083 = 2655125) B2655125
theorem B1049201 : Blo 698317 1049201 := bstep (se 2 (by rfl) ⟨393450, by rfl⟩ : syracuseStep 1049201 = 786901) B786901
theorem B1180291 : Blo 698317 1180291 := bstep (se 1 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 1180291 = 1770437) B1770437
theorem B1049219 : Blo 698317 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B1049249 : Blo 698317 1049249 := bstep (se 2 (by rfl) ⟨393468, by rfl⟩ : syracuseStep 1049249 = 786937) B786937
theorem B1704611 : Blo 698317 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B1049267 : Blo 698317 1049267 := bstep (se 1 (by rfl) ⟨786950, by rfl⟩ : syracuseStep 1049267 = 1573901) B1573901
theorem B1049297 : Blo 698317 1049297 := bstep (se 2 (by rfl) ⟨393486, by rfl⟩ : syracuseStep 1049297 = 786973) B786973
theorem B1049315 : Blo 698317 1049315 := bstep (se 1 (by rfl) ⟨786986, by rfl⟩ : syracuseStep 1049315 = 1573973) B1573973
theorem B787171 : Blo 698317 787171 := bstep (se 1 (by rfl) ⟨590378, by rfl⟩ : syracuseStep 787171 = 1180757) B1180757
theorem B1049345 : Blo 698317 1049345 := bstep (se 2 (by rfl) ⟨393504, by rfl⟩ : syracuseStep 1049345 = 787009) B787009
theorem B1573649 : Blo 698317 1573649 := bstep (se 2 (by rfl) ⟨590118, by rfl⟩ : syracuseStep 1573649 = 1180237) B1180237
theorem B1180433 : Blo 698317 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B1049363 : Blo 698317 1049363 := bstep (se 1 (by rfl) ⟨787022, by rfl⟩ : syracuseStep 1049363 = 1574045) B1574045
theorem B1770275 : Blo 698317 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B1573667 : Blo 698317 1573667 := bstep (se 1 (by rfl) ⟨1180250, by rfl⟩ : syracuseStep 1573667 = 2360501) B2360501
theorem B1049393 : Blo 698317 1049393 := bstep (se 2 (by rfl) ⟨393522, by rfl⟩ : syracuseStep 1049393 = 787045) B787045
theorem B1049411 : Blo 698317 1049411 := bstep (se 1 (by rfl) ⟨787058, by rfl⟩ : syracuseStep 1049411 = 1574117) B1574117
theorem B1049441 : Blo 698317 1049441 := bstep (se 2 (by rfl) ⟨393540, by rfl⟩ : syracuseStep 1049441 = 787081) B787081
theorem B2360177 : Blo 698317 2360177 := bstep (se 2 (by rfl) ⟨885066, by rfl⟩ : syracuseStep 2360177 = 1770133) B1770133
theorem B1049459 : Blo 698317 1049459 := bstep (se 1 (by rfl) ⟨787094, by rfl⟩ : syracuseStep 1049459 = 1574189) B1574189
theorem B787315 : Blo 698317 787315 := bstep (se 1 (by rfl) ⟨590486, by rfl⟩ : syracuseStep 787315 = 1180973) B1180973
theorem B2392973 : Blo 698317 2392973 := bstep (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) B897365
theorem B1180561 : Blo 698317 1180561 := bstep (se 2 (by rfl) ⟨442710, by rfl⟩ : syracuseStep 1180561 = 885421) B885421
theorem B1049489 : Blo 698317 1049489 := bstep (se 2 (by rfl) ⟨393558, by rfl⟩ : syracuseStep 1049489 = 787117) B787117
theorem B2655139 : Blo 698317 2655139 := bstep (se 1 (by rfl) ⟨1991354, by rfl⟩ : syracuseStep 2655139 = 3982709) B3982709
theorem B1049507 : Blo 698317 1049507 := bstep (se 1 (by rfl) ⟨787130, by rfl⟩ : syracuseStep 1049507 = 1574261) B1574261
theorem B1180595 : Blo 698317 1180595 := bstep (se 1 (by rfl) ⟨885446, by rfl⟩ : syracuseStep 1180595 = 1770893) B1770893
theorem B1049537 : Blo 698317 1049537 := bstep (se 2 (by rfl) ⟨393576, by rfl⟩ : syracuseStep 1049537 = 787153) B787153
theorem B1278929 : Blo 698317 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B1049555 : Blo 698317 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B1999853 : Blo 698317 1999853 := bstep (se 3 (by rfl) ⟨374972, by rfl⟩ : syracuseStep 1999853 = 749945) B749945
theorem B1049585 : Blo 698317 1049585 := bstep (se 2 (by rfl) ⟨393594, by rfl⟩ : syracuseStep 1049585 = 787189) B787189
theorem B1049603 : Blo 698317 1049603 := bstep (se 1 (by rfl) ⟨787202, by rfl⟩ : syracuseStep 1049603 = 1574405) B1574405
theorem B787459 : Blo 698317 787459 := bstep (se 1 (by rfl) ⟨590594, by rfl⟩ : syracuseStep 787459 = 1181189) B1181189
theorem B1049633 : Blo 698317 1049633 := bstep (se 2 (by rfl) ⟨393612, by rfl⟩ : syracuseStep 1049633 = 787225) B787225
theorem B1573937 : Blo 698317 1573937 := bstep (se 2 (by rfl) ⟨590226, by rfl⟩ : syracuseStep 1573937 = 1180453) B1180453
theorem B1180723 : Blo 698317 1180723 := bstep (se 1 (by rfl) ⟨885542, by rfl⟩ : syracuseStep 1180723 = 1771085) B1771085
theorem B1049651 : Blo 698317 1049651 := bstep (se 1 (by rfl) ⟨787238, by rfl⟩ : syracuseStep 1049651 = 1574477) B1574477
theorem B885811 : Blo 698317 885811 := bstep (se 1 (by rfl) ⟨664358, by rfl⟩ : syracuseStep 885811 = 1328717) B1328717
theorem B1573955 : Blo 698317 1573955 := bstep (se 1 (by rfl) ⟨1180466, by rfl⟩ : syracuseStep 1573955 = 2360933) B2360933
theorem B1049681 : Blo 698317 1049681 := bstep (se 2 (by rfl) ⟨393630, by rfl⟩ : syracuseStep 1049681 = 787261) B787261
theorem B1049699 : Blo 698317 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B2393201 : Blo 698317 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B1049729 : Blo 698317 1049729 := bstep (se 2 (by rfl) ⟨393648, by rfl⟩ : syracuseStep 1049729 = 787297) B787297
theorem B1049747 : Blo 698317 1049747 := bstep (se 1 (by rfl) ⟨787310, by rfl⟩ : syracuseStep 1049747 = 1574621) B1574621
theorem B885907 : Blo 698317 885907 := bstep (se 1 (by rfl) ⟨664430, by rfl⟩ : syracuseStep 885907 = 1328861) B1328861
theorem B787603 : Blo 698317 787603 := bstep (se 1 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 787603 = 1181405) B1181405
theorem B1049777 : Blo 698317 1049777 := bstep (se 2 (by rfl) ⟨393666, by rfl⟩ : syracuseStep 1049777 = 787333) B787333
theorem B1180865 : Blo 698317 1180865 := bstep (se 2 (by rfl) ⟨442824, by rfl⟩ : syracuseStep 1180865 = 885649) B885649
theorem B1049795 : Blo 698317 1049795 := bstep (se 1 (by rfl) ⟨787346, by rfl⟩ : syracuseStep 1049795 = 1574693) B1574693
theorem B1049825 : Blo 698317 1049825 := bstep (se 2 (by rfl) ⟨393684, by rfl⟩ : syracuseStep 1049825 = 787369) B787369
theorem B1049843 : Blo 698317 1049843 := bstep (se 1 (by rfl) ⟨787382, by rfl⟩ : syracuseStep 1049843 = 1574765) B1574765
theorem B1279235 : Blo 698317 1279235 := bstep (se 1 (by rfl) ⟨959426, by rfl⟩ : syracuseStep 1279235 = 1918853) B1918853
theorem B1049873 : Blo 698317 1049873 := bstep (se 2 (by rfl) ⟨393702, by rfl⟩ : syracuseStep 1049873 = 787405) B787405
theorem B1049891 : Blo 698317 1049891 := bstep (se 1 (by rfl) ⟨787418, by rfl⟩ : syracuseStep 1049891 = 1574837) B1574837
theorem B787747 : Blo 698317 787747 := bstep (se 1 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 787747 = 1181621) B1181621
theorem B1180993 : Blo 698317 1180993 := bstep (se 2 (by rfl) ⟨442872, by rfl⟩ : syracuseStep 1180993 = 885745) B885745
theorem B1049921 : Blo 698317 1049921 := bstep (se 2 (by rfl) ⟨393720, by rfl⟩ : syracuseStep 1049921 = 787441) B787441
theorem B1574225 : Blo 698317 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B1049939 : Blo 698317 1049939 := bstep (se 1 (by rfl) ⟨787454, by rfl⟩ : syracuseStep 1049939 = 1574909) B1574909
theorem B1574243 : Blo 698317 1574243 := bstep (se 1 (by rfl) ⟨1180682, by rfl⟩ : syracuseStep 1574243 = 2361365) B2361365
theorem B1181027 : Blo 698317 1181027 := bstep (se 1 (by rfl) ⟨885770, by rfl⟩ : syracuseStep 1181027 = 1771541) B1771541
theorem B1049969 : Blo 698317 1049969 := bstep (se 2 (by rfl) ⟨393738, by rfl⟩ : syracuseStep 1049969 = 787477) B787477
theorem B1049987 : Blo 698317 1049987 := bstep (se 1 (by rfl) ⟨787490, by rfl⟩ : syracuseStep 1049987 = 1574981) B1574981
theorem B2360717 : Blo 698317 2360717 := bstep (se 3 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 2360717 = 885269) B885269
theorem B1050017 : Blo 698317 1050017 := bstep (se 2 (by rfl) ⟨393756, by rfl⟩ : syracuseStep 1050017 = 787513) B787513
theorem B1050035 : Blo 698317 1050035 := bstep (se 1 (by rfl) ⟨787526, by rfl⟩ : syracuseStep 1050035 = 1575053) B1575053
theorem B787891 : Blo 698317 787891 := bstep (se 1 (by rfl) ⟨590918, by rfl⟩ : syracuseStep 787891 = 1181837) B1181837
theorem B2360771 : Blo 698317 2360771 := bstep (se 1 (by rfl) ⟨1770578, by rfl⟩ : syracuseStep 2360771 = 3541157) B3541157
theorem B1050065 : Blo 698317 1050065 := bstep (se 2 (by rfl) ⟨393774, by rfl⟩ : syracuseStep 1050065 = 787549) B787549
theorem B1181155 : Blo 698317 1181155 := bstep (se 1 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 1181155 = 1771733) B1771733
theorem B1050083 : Blo 698317 1050083 := bstep (se 1 (by rfl) ⟨787562, by rfl⟩ : syracuseStep 1050083 = 1575125) B1575125
theorem B3999203 : Blo 698317 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B2164205 : Blo 698317 2164205 := bstep (se 3 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 2164205 = 811577) B811577
theorem B1050113 : Blo 698317 1050113 := bstep (se 2 (by rfl) ⟨393792, by rfl⟩ : syracuseStep 1050113 = 787585) B787585
theorem B1050131 : Blo 698317 1050131 := bstep (se 1 (by rfl) ⟨787598, by rfl⟩ : syracuseStep 1050131 = 1575197) B1575197
theorem B1050161 : Blo 698317 1050161 := bstep (se 2 (by rfl) ⟨393810, by rfl⟩ : syracuseStep 1050161 = 787621) B787621
theorem B4490801 : Blo 698317 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B1050179 : Blo 698317 1050179 := bstep (se 1 (by rfl) ⟨787634, by rfl⟩ : syracuseStep 1050179 = 1575269) B1575269
theorem B788035 : Blo 698317 788035 := bstep (se 1 (by rfl) ⟨591026, by rfl⟩ : syracuseStep 788035 = 1182053) B1182053
theorem B1050209 : Blo 698317 1050209 := bstep (se 2 (by rfl) ⟨393828, by rfl⟩ : syracuseStep 1050209 = 787657) B787657
theorem B1574513 : Blo 698317 1574513 := bstep (se 2 (by rfl) ⟨590442, by rfl⟩ : syracuseStep 1574513 = 1180885) B1180885
theorem B1181297 : Blo 698317 1181297 := bstep (se 2 (by rfl) ⟨442986, by rfl⟩ : syracuseStep 1181297 = 885973) B885973
theorem B1050227 : Blo 698317 1050227 := bstep (se 1 (by rfl) ⟨787670, by rfl⟩ : syracuseStep 1050227 = 1575341) B1575341
theorem B1574531 : Blo 698317 1574531 := bstep (se 1 (by rfl) ⟨1180898, by rfl⟩ : syracuseStep 1574531 = 2361797) B2361797
theorem B886403 : Blo 698317 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B1050257 : Blo 698317 1050257 := bstep (se 2 (by rfl) ⟨393846, by rfl⟩ : syracuseStep 1050257 = 787693) B787693
theorem B1050275 : Blo 698317 1050275 := bstep (se 1 (by rfl) ⟨787706, by rfl⟩ : syracuseStep 1050275 = 1575413) B1575413
theorem B1050305 : Blo 698317 1050305 := bstep (se 2 (by rfl) ⟨393864, by rfl⟩ : syracuseStep 1050305 = 787729) B787729
theorem B2164429 : Blo 698317 2164429 := bstep (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) B811661
theorem B2361041 : Blo 698317 2361041 := bstep (se 2 (by rfl) ⟨885390, by rfl⟩ : syracuseStep 2361041 = 1770781) B1770781
theorem B1771217 : Blo 698317 1771217 := bstep (se 2 (by rfl) ⟨664206, by rfl⟩ : syracuseStep 1771217 = 1328413) B1328413
theorem B1050323 : Blo 698317 1050323 := bstep (se 1 (by rfl) ⟨787742, by rfl⟩ : syracuseStep 1050323 = 1575485) B1575485
theorem B788179 : Blo 698317 788179 := bstep (se 1 (by rfl) ⟨591134, by rfl⟩ : syracuseStep 788179 = 1182269) B1182269
theorem B1181425 : Blo 698317 1181425 := bstep (se 2 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 1181425 = 886069) B886069
theorem B1050353 : Blo 698317 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B1771267 : Blo 698317 1771267 := bstep (se 1 (by rfl) ⟨1328450, by rfl⟩ : syracuseStep 1771267 = 2656901) B2656901
theorem B1050371 : Blo 698317 1050371 := bstep (se 1 (by rfl) ⟨787778, by rfl⟩ : syracuseStep 1050371 = 1575557) B1575557
theorem B1181459 : Blo 698317 1181459 := bstep (se 1 (by rfl) ⟨886094, by rfl⟩ : syracuseStep 1181459 = 1772189) B1772189
theorem B1050401 : Blo 698317 1050401 := bstep (se 2 (by rfl) ⟨393900, by rfl⟩ : syracuseStep 1050401 = 787801) B787801
theorem B1050419 : Blo 698317 1050419 := bstep (se 1 (by rfl) ⟨787814, by rfl⟩ : syracuseStep 1050419 = 1575629) B1575629
theorem B1050449 : Blo 698317 1050449 := bstep (se 2 (by rfl) ⟨393918, by rfl⟩ : syracuseStep 1050449 = 787837) B787837
theorem B1050467 : Blo 698317 1050467 := bstep (se 1 (by rfl) ⟨787850, by rfl⟩ : syracuseStep 1050467 = 1575701) B1575701
theorem B788323 : Blo 698317 788323 := bstep (se 1 (by rfl) ⟨591242, by rfl⟩ : syracuseStep 788323 = 1182485) B1182485
theorem B1050497 : Blo 698317 1050497 := bstep (se 2 (by rfl) ⟨393936, by rfl⟩ : syracuseStep 1050497 = 787873) B787873
theorem B1771409 : Blo 698317 1771409 := bstep (se 2 (by rfl) ⟨664278, by rfl⟩ : syracuseStep 1771409 = 1328557) B1328557
theorem B1574801 : Blo 698317 1574801 := bstep (se 2 (by rfl) ⟨590550, by rfl⟩ : syracuseStep 1574801 = 1181101) B1181101
theorem B1181587 : Blo 698317 1181587 := bstep (se 1 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 1181587 = 1772381) B1772381
theorem B1050515 : Blo 698317 1050515 := bstep (se 1 (by rfl) ⟨787886, by rfl⟩ : syracuseStep 1050515 = 1575773) B1575773
theorem B1574819 : Blo 698317 1574819 := bstep (se 1 (by rfl) ⟨1181114, by rfl⟩ : syracuseStep 1574819 = 2362229) B2362229
theorem B1050545 : Blo 698317 1050545 := bstep (se 2 (by rfl) ⟨393954, by rfl⟩ : syracuseStep 1050545 = 787909) B787909
theorem B1050563 : Blo 698317 1050563 := bstep (se 1 (by rfl) ⟨787922, by rfl⟩ : syracuseStep 1050563 = 1575845) B1575845
theorem B1050593 : Blo 698317 1050593 := bstep (se 2 (by rfl) ⟨393972, by rfl⟩ : syracuseStep 1050593 = 787945) B787945
theorem B1050611 : Blo 698317 1050611 := bstep (se 1 (by rfl) ⟨787958, by rfl⟩ : syracuseStep 1050611 = 1575917) B1575917
theorem B788467 : Blo 698317 788467 := bstep (se 1 (by rfl) ⟨591350, by rfl⟩ : syracuseStep 788467 = 1182701) B1182701
theorem B1050641 : Blo 698317 1050641 := bstep (se 2 (by rfl) ⟨393990, by rfl⟩ : syracuseStep 1050641 = 787981) B787981
theorem B1181729 : Blo 698317 1181729 := bstep (se 2 (by rfl) ⟨443148, by rfl⟩ : syracuseStep 1181729 = 886297) B886297
theorem B1050659 : Blo 698317 1050659 := bstep (se 1 (by rfl) ⟨787994, by rfl⟩ : syracuseStep 1050659 = 1575989) B1575989
theorem B1050689 : Blo 698317 1050689 := bstep (se 2 (by rfl) ⟨394008, by rfl⟩ : syracuseStep 1050689 = 788017) B788017
theorem B6719557 : Blo 698317 6719557 := bstep (se 4 (by rfl) ⟨629958, by rfl⟩ : syracuseStep 6719557 = 1259917) B1259917
theorem B1050707 : Blo 698317 1050707 := bstep (se 1 (by rfl) ⟨788030, by rfl⟩ : syracuseStep 1050707 = 1576061) B1576061
theorem B30673009 : Blo 698317 30673009 := bstep (se 2 (by rfl) ⟨11502378, by rfl⟩ : syracuseStep 30673009 = 23004757) B23004757
theorem B1050737 : Blo 698317 1050737 := bstep (se 2 (by rfl) ⟨394026, by rfl⟩ : syracuseStep 1050737 = 788053) B788053
theorem B1050755 : Blo 698317 1050755 := bstep (se 1 (by rfl) ⟨788066, by rfl⟩ : syracuseStep 1050755 = 1576133) B1576133
theorem B788611 : Blo 698317 788611 := bstep (se 1 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 788611 = 1182917) B1182917
theorem B1181857 : Blo 698317 1181857 := bstep (se 2 (by rfl) ⟨443196, by rfl⟩ : syracuseStep 1181857 = 886393) B886393
theorem B1050785 : Blo 698317 1050785 := bstep (se 2 (by rfl) ⟨394044, by rfl⟩ : syracuseStep 1050785 = 788089) B788089
theorem B1575089 : Blo 698317 1575089 := bstep (se 2 (by rfl) ⟨590658, by rfl⟩ : syracuseStep 1575089 = 1181317) B1181317
theorem B1050803 : Blo 698317 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B1575107 : Blo 698317 1575107 := bstep (se 1 (by rfl) ⟨1181330, by rfl⟩ : syracuseStep 1575107 = 2362661) B2362661
theorem B1181891 : Blo 698317 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B1050833 : Blo 698317 1050833 := bstep (se 2 (by rfl) ⟨394062, by rfl⟩ : syracuseStep 1050833 = 788125) B788125
theorem B1050851 : Blo 698317 1050851 := bstep (se 1 (by rfl) ⟨788138, by rfl⟩ : syracuseStep 1050851 = 1576277) B1576277
theorem B2361581 : Blo 698317 2361581 := bstep (se 3 (by rfl) ⟨442796, by rfl⟩ : syracuseStep 2361581 = 885593) B885593
theorem B1050881 : Blo 698317 1050881 := bstep (se 2 (by rfl) ⟨394080, by rfl⟩ : syracuseStep 1050881 = 788161) B788161
theorem B1050899 : Blo 698317 1050899 := bstep (se 1 (by rfl) ⟨788174, by rfl⟩ : syracuseStep 1050899 = 1576349) B1576349
theorem B788755 : Blo 698317 788755 := bstep (se 1 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 788755 = 1183133) B1183133
theorem B2361635 : Blo 698317 2361635 := bstep (se 1 (by rfl) ⟨1771226, by rfl⟩ : syracuseStep 2361635 = 3542453) B3542453
theorem B1050929 : Blo 698317 1050929 := bstep (se 2 (by rfl) ⟨394098, by rfl⟩ : syracuseStep 1050929 = 788197) B788197
theorem B1182019 : Blo 698317 1182019 := bstep (se 1 (by rfl) ⟨886514, by rfl⟩ : syracuseStep 1182019 = 1773029) B1773029
theorem B1050947 : Blo 698317 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B887107 : Blo 698317 887107 := bstep (se 1 (by rfl) ⟨665330, by rfl⟩ : syracuseStep 887107 = 1330661) B1330661
theorem B1050977 : Blo 698317 1050977 := bstep (se 2 (by rfl) ⟨394116, by rfl⟩ : syracuseStep 1050977 = 788233) B788233
theorem B1050995 : Blo 698317 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B1051025 : Blo 698317 1051025 := bstep (se 2 (by rfl) ⟨394134, by rfl⟩ : syracuseStep 1051025 = 788269) B788269
theorem B1051043 : Blo 698317 1051043 := bstep (se 1 (by rfl) ⟨788282, by rfl⟩ : syracuseStep 1051043 = 1576565) B1576565
theorem B887203 : Blo 698317 887203 := bstep (se 1 (by rfl) ⟨665402, by rfl⟩ : syracuseStep 887203 = 1330805) B1330805
theorem B788899 : Blo 698317 788899 := bstep (se 1 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 788899 = 1183349) B1183349
theorem B1051073 : Blo 698317 1051073 := bstep (se 2 (by rfl) ⟨394152, by rfl⟩ : syracuseStep 1051073 = 788305) B788305
theorem B1575377 : Blo 698317 1575377 := bstep (se 2 (by rfl) ⟨590766, by rfl⟩ : syracuseStep 1575377 = 1181533) B1181533
theorem B1182161 : Blo 698317 1182161 := bstep (se 2 (by rfl) ⟨443310, by rfl⟩ : syracuseStep 1182161 = 886621) B886621
theorem B1051091 : Blo 698317 1051091 := bstep (se 1 (by rfl) ⟨788318, by rfl⟩ : syracuseStep 1051091 = 1576637) B1576637
theorem B1575395 : Blo 698317 1575395 := bstep (se 1 (by rfl) ⟨1181546, by rfl⟩ : syracuseStep 1575395 = 2363093) B2363093
theorem B1051121 : Blo 698317 1051121 := bstep (se 2 (by rfl) ⟨394170, by rfl⟩ : syracuseStep 1051121 = 788341) B788341
theorem B1051139 : Blo 698317 1051139 := bstep (se 1 (by rfl) ⟨788354, by rfl⟩ : syracuseStep 1051139 = 1576709) B1576709
theorem B1051169 : Blo 698317 1051169 := bstep (se 2 (by rfl) ⟨394188, by rfl⟩ : syracuseStep 1051169 = 788377) B788377
theorem B2361905 : Blo 698317 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B1051187 : Blo 698317 1051187 := bstep (se 1 (by rfl) ⟨788390, by rfl⟩ : syracuseStep 1051187 = 1576781) B1576781
theorem B789043 : Blo 698317 789043 := bstep (se 1 (by rfl) ⟨591782, by rfl⟩ : syracuseStep 789043 = 1183565) B1183565
theorem B1182289 : Blo 698317 1182289 := bstep (se 2 (by rfl) ⟨443358, by rfl⟩ : syracuseStep 1182289 = 886717) B886717
theorem B1051217 : Blo 698317 1051217 := bstep (se 2 (by rfl) ⟨394206, by rfl⟩ : syracuseStep 1051217 = 788413) B788413
theorem B1051235 : Blo 698317 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B1182323 : Blo 698317 1182323 := bstep (se 1 (by rfl) ⟨886742, by rfl⟩ : syracuseStep 1182323 = 1773485) B1773485
theorem B1051265 : Blo 698317 1051265 := bstep (se 2 (by rfl) ⟨394224, by rfl⟩ : syracuseStep 1051265 = 788449) B788449
theorem B1051283 : Blo 698317 1051283 := bstep (se 1 (by rfl) ⟨788462, by rfl⟩ : syracuseStep 1051283 = 1576925) B1576925
theorem B1051313 : Blo 698317 1051313 := bstep (se 2 (by rfl) ⟨394242, by rfl⟩ : syracuseStep 1051313 = 788485) B788485
theorem B1051331 : Blo 698317 1051331 := bstep (se 1 (by rfl) ⟨788498, by rfl⟩ : syracuseStep 1051331 = 1576997) B1576997
theorem B789187 : Blo 698317 789187 := bstep (se 1 (by rfl) ⟨591890, by rfl⟩ : syracuseStep 789187 = 1183781) B1183781
theorem B11340485 : Blo 698317 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B8981189 : Blo 698317 8981189 := bstep (se 4 (by rfl) ⟨841986, by rfl⟩ : syracuseStep 8981189 = 1683973) B1683973
theorem B1051361 : Blo 698317 1051361 := bstep (se 2 (by rfl) ⟨394260, by rfl⟩ : syracuseStep 1051361 = 788521) B788521
theorem B1575665 : Blo 698317 1575665 := bstep (se 2 (by rfl) ⟨590874, by rfl⟩ : syracuseStep 1575665 = 1181749) B1181749
theorem B1182451 : Blo 698317 1182451 := bstep (se 1 (by rfl) ⟨886838, by rfl⟩ : syracuseStep 1182451 = 1773677) B1773677
theorem B1051379 : Blo 698317 1051379 := bstep (se 1 (by rfl) ⟨788534, by rfl⟩ : syracuseStep 1051379 = 1577069) B1577069
theorem B1575683 : Blo 698317 1575683 := bstep (se 1 (by rfl) ⟨1181762, by rfl⟩ : syracuseStep 1575683 = 2363525) B2363525
theorem B1051409 : Blo 698317 1051409 := bstep (se 2 (by rfl) ⟨394278, by rfl⟩ : syracuseStep 1051409 = 788557) B788557
theorem B1051427 : Blo 698317 1051427 := bstep (se 1 (by rfl) ⟨788570, by rfl⟩ : syracuseStep 1051427 = 1577141) B1577141
theorem B1051457 : Blo 698317 1051457 := bstep (se 2 (by rfl) ⟨394296, by rfl⟩ : syracuseStep 1051457 = 788593) B788593
theorem B1051475 : Blo 698317 1051475 := bstep (se 1 (by rfl) ⟨788606, by rfl⟩ : syracuseStep 1051475 = 1577213) B1577213
theorem B789331 : Blo 698317 789331 := bstep (se 1 (by rfl) ⟨591998, by rfl⟩ : syracuseStep 789331 = 1183997) B1183997
theorem B1772401 : Blo 698317 1772401 := bstep (se 2 (by rfl) ⟨664650, by rfl⟩ : syracuseStep 1772401 = 1329301) B1329301
theorem B1051505 : Blo 698317 1051505 := bstep (se 2 (by rfl) ⟨394314, by rfl⟩ : syracuseStep 1051505 = 788629) B788629
theorem B1182593 : Blo 698317 1182593 := bstep (se 2 (by rfl) ⟨443472, by rfl⟩ : syracuseStep 1182593 = 886945) B886945
theorem B1051523 : Blo 698317 1051523 := bstep (se 1 (by rfl) ⟨788642, by rfl⟩ : syracuseStep 1051523 = 1577285) B1577285
theorem B2984845 : Blo 698317 2984845 := bstep (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) B1119317
theorem B887699 : Blo 698317 887699 := bstep (se 1 (by rfl) ⟨665774, by rfl⟩ : syracuseStep 887699 = 1331549) B1331549
theorem B1051553 : Blo 698317 1051553 := bstep (se 2 (by rfl) ⟨394332, by rfl⟩ : syracuseStep 1051553 = 788665) B788665
theorem B1051571 : Blo 698317 1051571 := bstep (se 1 (by rfl) ⟨788678, by rfl⟩ : syracuseStep 1051571 = 1577357) B1577357
theorem B1051601 : Blo 698317 1051601 := bstep (se 2 (by rfl) ⟨394350, by rfl⟩ : syracuseStep 1051601 = 788701) B788701
theorem B1051619 : Blo 698317 1051619 := bstep (se 1 (by rfl) ⟨788714, by rfl⟩ : syracuseStep 1051619 = 1577429) B1577429
theorem B789475 : Blo 698317 789475 := bstep (se 1 (by rfl) ⟨592106, by rfl⟩ : syracuseStep 789475 = 1184213) B1184213
theorem B1182721 : Blo 698317 1182721 := bstep (se 2 (by rfl) ⟨443520, by rfl⟩ : syracuseStep 1182721 = 887041) B887041
theorem B1051649 : Blo 698317 1051649 := bstep (se 2 (by rfl) ⟨394368, by rfl⟩ : syracuseStep 1051649 = 788737) B788737
theorem B1575953 : Blo 698317 1575953 := bstep (se 2 (by rfl) ⟨590982, by rfl⟩ : syracuseStep 1575953 = 1181965) B1181965
theorem B1051667 : Blo 698317 1051667 := bstep (se 1 (by rfl) ⟨788750, by rfl⟩ : syracuseStep 1051667 = 1577501) B1577501
theorem B1575971 : Blo 698317 1575971 := bstep (se 1 (by rfl) ⟨1181978, by rfl⟩ : syracuseStep 1575971 = 2363957) B2363957
theorem B1182755 : Blo 698317 1182755 := bstep (se 1 (by rfl) ⟨887066, by rfl⟩ : syracuseStep 1182755 = 1774133) B1774133
theorem B1051697 : Blo 698317 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B1051715 : Blo 698317 1051715 := bstep (se 1 (by rfl) ⟨788786, by rfl⟩ : syracuseStep 1051715 = 1577573) B1577573
theorem B2657357 : Blo 698317 2657357 := bstep (se 3 (by rfl) ⟨498254, by rfl⟩ : syracuseStep 2657357 = 996509) B996509
theorem B2362445 : Blo 698317 2362445 := bstep (se 3 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 2362445 = 885917) B885917
theorem B1051745 : Blo 698317 1051745 := bstep (se 2 (by rfl) ⟨394404, by rfl⟩ : syracuseStep 1051745 = 788809) B788809
theorem B3542129 : Blo 698317 3542129 := bstep (se 2 (by rfl) ⟨1328298, by rfl⟩ : syracuseStep 3542129 = 2656597) B2656597
theorem B1051763 : Blo 698317 1051763 := bstep (se 1 (by rfl) ⟨788822, by rfl⟩ : syracuseStep 1051763 = 1577645) B1577645
theorem B789619 : Blo 698317 789619 := bstep (se 1 (by rfl) ⟨592214, by rfl⟩ : syracuseStep 789619 = 1184429) B1184429
theorem B2362499 : Blo 698317 2362499 := bstep (se 1 (by rfl) ⟨1771874, by rfl⟩ : syracuseStep 2362499 = 3543749) B3543749
theorem B1772675 : Blo 698317 1772675 := bstep (se 1 (by rfl) ⟨1329506, by rfl⟩ : syracuseStep 1772675 = 2659013) B2659013
theorem B1051793 : Blo 698317 1051793 := bstep (se 2 (by rfl) ⟨394422, by rfl⟩ : syracuseStep 1051793 = 788845) B788845
theorem B1182883 : Blo 698317 1182883 := bstep (se 1 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 1182883 = 1774325) B1774325
theorem B1051811 : Blo 698317 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B1051841 : Blo 698317 1051841 := bstep (se 2 (by rfl) ⟨394440, by rfl⟩ : syracuseStep 1051841 = 788881) B788881
theorem B4492493 : Blo 698317 4492493 := bstep (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) B1684685
theorem B1051859 : Blo 698317 1051859 := bstep (se 1 (by rfl) ⟨788894, by rfl⟩ : syracuseStep 1051859 = 1577789) B1577789
theorem B2985187 : Blo 698317 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B1051889 : Blo 698317 1051889 := bstep (se 2 (by rfl) ⟨394458, by rfl⟩ : syracuseStep 1051889 = 788917) B788917
theorem B1051907 : Blo 698317 1051907 := bstep (se 1 (by rfl) ⟨788930, by rfl⟩ : syracuseStep 1051907 = 1577861) B1577861
theorem B789763 : Blo 698317 789763 := bstep (se 1 (by rfl) ⟨592322, by rfl⟩ : syracuseStep 789763 = 1184645) B1184645
theorem B1051937 : Blo 698317 1051937 := bstep (se 2 (by rfl) ⟨394476, by rfl⟩ : syracuseStep 1051937 = 788953) B788953
theorem B1576241 : Blo 698317 1576241 := bstep (se 2 (by rfl) ⟨591090, by rfl⟩ : syracuseStep 1576241 = 1182181) B1182181
theorem B1183025 : Blo 698317 1183025 := bstep (se 2 (by rfl) ⟨443634, by rfl⟩ : syracuseStep 1183025 = 887269) B887269
theorem B1051955 : Blo 698317 1051955 := bstep (se 1 (by rfl) ⟨788966, by rfl⟩ : syracuseStep 1051955 = 1577933) B1577933
theorem B1772867 : Blo 698317 1772867 := bstep (se 1 (by rfl) ⟨1329650, by rfl⟩ : syracuseStep 1772867 = 2659301) B2659301
theorem B1576259 : Blo 698317 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B1051985 : Blo 698317 1051985 := bstep (se 2 (by rfl) ⟨394494, by rfl⟩ : syracuseStep 1051985 = 788989) B788989
theorem B1052003 : Blo 698317 1052003 := bstep (se 1 (by rfl) ⟨789002, by rfl⟩ : syracuseStep 1052003 = 1578005) B1578005
theorem B1052033 : Blo 698317 1052033 := bstep (se 2 (by rfl) ⟨394512, by rfl⟩ : syracuseStep 1052033 = 789025) B789025
theorem B2362769 : Blo 698317 2362769 := bstep (se 2 (by rfl) ⟨886038, by rfl⟩ : syracuseStep 2362769 = 1772077) B1772077
theorem B1052051 : Blo 698317 1052051 := bstep (se 1 (by rfl) ⟨789038, by rfl⟩ : syracuseStep 1052051 = 1578077) B1578077
theorem B789907 : Blo 698317 789907 := bstep (se 1 (by rfl) ⟨592430, by rfl⟩ : syracuseStep 789907 = 1184861) B1184861
theorem B1183153 : Blo 698317 1183153 := bstep (se 2 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 1183153 = 887365) B887365
theorem B1052081 : Blo 698317 1052081 := bstep (se 2 (by rfl) ⟨394530, by rfl⟩ : syracuseStep 1052081 = 789061) B789061
theorem B1052099 : Blo 698317 1052099 := bstep (se 1 (by rfl) ⟨789074, by rfl⟩ : syracuseStep 1052099 = 1578149) B1578149
theorem B2395601 : Blo 698317 2395601 := bstep (se 2 (by rfl) ⟨898350, by rfl⟩ : syracuseStep 2395601 = 1796701) B1796701
theorem B1183187 : Blo 698317 1183187 := bstep (se 1 (by rfl) ⟨887390, by rfl⟩ : syracuseStep 1183187 = 1774781) B1774781
theorem B1052129 : Blo 698317 1052129 := bstep (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) B789097
theorem B1052147 : Blo 698317 1052147 := bstep (se 1 (by rfl) ⟨789110, by rfl⟩ : syracuseStep 1052147 = 1578221) B1578221
theorem B1052177 : Blo 698317 1052177 := bstep (se 2 (by rfl) ⟨394566, by rfl⟩ : syracuseStep 1052177 = 789133) B789133
theorem B1052195 : Blo 698317 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B790051 : Blo 698317 790051 := bstep (se 1 (by rfl) ⟨592538, by rfl⟩ : syracuseStep 790051 = 1185077) B1185077
theorem B1052225 : Blo 698317 1052225 := bstep (se 2 (by rfl) ⟨394584, by rfl⟩ : syracuseStep 1052225 = 789169) B789169
theorem B1576529 : Blo 698317 1576529 := bstep (se 2 (by rfl) ⟨591198, by rfl⟩ : syracuseStep 1576529 = 1182397) B1182397
theorem B1183315 : Blo 698317 1183315 := bstep (se 1 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 1183315 = 1774973) B1774973
theorem B1052243 : Blo 698317 1052243 := bstep (se 1 (by rfl) ⟨789182, by rfl⟩ : syracuseStep 1052243 = 1578365) B1578365
theorem B888403 : Blo 698317 888403 := bstep (se 1 (by rfl) ⟨666302, by rfl⟩ : syracuseStep 888403 = 1332605) B1332605
theorem B1576547 : Blo 698317 1576547 := bstep (se 1 (by rfl) ⟨1182410, by rfl⟩ : syracuseStep 1576547 = 2364821) B2364821
theorem B1052273 : Blo 698317 1052273 := bstep (se 2 (by rfl) ⟨394602, by rfl⟩ : syracuseStep 1052273 = 789205) B789205
theorem B1052291 : Blo 698317 1052291 := bstep (se 1 (by rfl) ⟨789218, by rfl⟩ : syracuseStep 1052291 = 1578437) B1578437
theorem B1052321 : Blo 698317 1052321 := bstep (se 2 (by rfl) ⟨394620, by rfl⟩ : syracuseStep 1052321 = 789241) B789241
theorem B1052339 : Blo 698317 1052339 := bstep (se 1 (by rfl) ⟨789254, by rfl⟩ : syracuseStep 1052339 = 1578509) B1578509
theorem B888499 : Blo 698317 888499 := bstep (se 1 (by rfl) ⟨666374, by rfl⟩ : syracuseStep 888499 = 1332749) B1332749
theorem B1052369 : Blo 698317 1052369 := bstep (se 2 (by rfl) ⟨394638, by rfl⟩ : syracuseStep 1052369 = 789277) B789277
theorem B1183457 : Blo 698317 1183457 := bstep (se 2 (by rfl) ⟨443796, by rfl⟩ : syracuseStep 1183457 = 887593) B887593
theorem B1052387 : Blo 698317 1052387 := bstep (se 1 (by rfl) ⟨789290, by rfl⟩ : syracuseStep 1052387 = 1578581) B1578581
theorem B1052417 : Blo 698317 1052417 := bstep (se 2 (by rfl) ⟨394656, by rfl⟩ : syracuseStep 1052417 = 789313) B789313
theorem B1052435 : Blo 698317 1052435 := bstep (se 1 (by rfl) ⟨789326, by rfl⟩ : syracuseStep 1052435 = 1578653) B1578653
theorem B2395939 : Blo 698317 2395939 := bstep (se 1 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 2395939 = 3593909) B3593909
theorem B1052465 : Blo 698317 1052465 := bstep (se 2 (by rfl) ⟨394674, by rfl⟩ : syracuseStep 1052465 = 789349) B789349
theorem B1052483 : Blo 698317 1052483 := bstep (se 1 (by rfl) ⟨789362, by rfl⟩ : syracuseStep 1052483 = 1578725) B1578725
theorem B1183585 : Blo 698317 1183585 := bstep (se 2 (by rfl) ⟨443844, by rfl⟩ : syracuseStep 1183585 = 887689) B887689
theorem B1052513 : Blo 698317 1052513 := bstep (se 2 (by rfl) ⟨394692, by rfl⟩ : syracuseStep 1052513 = 789385) B789385
theorem B1576817 : Blo 698317 1576817 := bstep (se 2 (by rfl) ⟨591306, by rfl⟩ : syracuseStep 1576817 = 1182613) B1182613
theorem B1052531 : Blo 698317 1052531 := bstep (se 1 (by rfl) ⟨789398, by rfl⟩ : syracuseStep 1052531 = 1578797) B1578797
theorem B1576835 : Blo 698317 1576835 := bstep (se 1 (by rfl) ⟨1182626, by rfl⟩ : syracuseStep 1576835 = 2365253) B2365253
theorem B1707907 : Blo 698317 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B1183619 : Blo 698317 1183619 := bstep (se 1 (by rfl) ⟨887714, by rfl⟩ : syracuseStep 1183619 = 1775429) B1775429
theorem B1052561 : Blo 698317 1052561 := bstep (se 2 (by rfl) ⟨394710, by rfl⟩ : syracuseStep 1052561 = 789421) B789421
theorem B1052579 : Blo 698317 1052579 := bstep (se 1 (by rfl) ⟨789434, by rfl⟩ : syracuseStep 1052579 = 1578869) B1578869
theorem B2363309 : Blo 698317 2363309 := bstep (se 3 (by rfl) ⟨443120, by rfl⟩ : syracuseStep 2363309 = 886241) B886241
theorem B1052609 : Blo 698317 1052609 := bstep (se 2 (by rfl) ⟨394728, by rfl⟩ : syracuseStep 1052609 = 789457) B789457
theorem B1052627 : Blo 698317 1052627 := bstep (se 1 (by rfl) ⟨789470, by rfl⟩ : syracuseStep 1052627 = 1578941) B1578941
theorem B2363363 : Blo 698317 2363363 := bstep (se 1 (by rfl) ⟨1772522, by rfl⟩ : syracuseStep 2363363 = 3545045) B3545045
theorem B1052657 : Blo 698317 1052657 := bstep (se 2 (by rfl) ⟨394746, by rfl⟩ : syracuseStep 1052657 = 789493) B789493
theorem B1183747 : Blo 698317 1183747 := bstep (se 1 (by rfl) ⟨887810, by rfl⟩ : syracuseStep 1183747 = 1775621) B1775621
theorem B1052675 : Blo 698317 1052675 := bstep (se 1 (by rfl) ⟨789506, by rfl⟩ : syracuseStep 1052675 = 1579013) B1579013
theorem B1052705 : Blo 698317 1052705 := bstep (se 2 (by rfl) ⟨394764, by rfl⟩ : syracuseStep 1052705 = 789529) B789529
theorem B1052723 : Blo 698317 1052723 := bstep (se 1 (by rfl) ⟨789542, by rfl⟩ : syracuseStep 1052723 = 1579085) B1579085
theorem B1052753 : Blo 698317 1052753 := bstep (se 2 (by rfl) ⟨394782, by rfl⟩ : syracuseStep 1052753 = 789565) B789565
theorem B1052771 : Blo 698317 1052771 := bstep (se 1 (by rfl) ⟨789578, by rfl⟩ : syracuseStep 1052771 = 1579157) B1579157
theorem B1052801 : Blo 698317 1052801 := bstep (se 2 (by rfl) ⟨394800, by rfl⟩ : syracuseStep 1052801 = 789601) B789601
theorem B1577105 : Blo 698317 1577105 := bstep (se 2 (by rfl) ⟨591414, by rfl⟩ : syracuseStep 1577105 = 1182829) B1182829
theorem B1183889 : Blo 698317 1183889 := bstep (se 2 (by rfl) ⟨443958, by rfl⟩ : syracuseStep 1183889 = 887917) B887917
theorem B1052819 : Blo 698317 1052819 := bstep (se 1 (by rfl) ⟨789614, by rfl⟩ : syracuseStep 1052819 = 1579229) B1579229
theorem B1577123 : Blo 698317 1577123 := bstep (se 1 (by rfl) ⟨1182842, by rfl⟩ : syracuseStep 1577123 = 2365685) B2365685
theorem B1052849 : Blo 698317 1052849 := bstep (se 2 (by rfl) ⟨394818, by rfl⟩ : syracuseStep 1052849 = 789637) B789637
theorem B1052867 : Blo 698317 1052867 := bstep (se 1 (by rfl) ⟨789650, by rfl⟩ : syracuseStep 1052867 = 1579301) B1579301
theorem B1052897 : Blo 698317 1052897 := bstep (se 2 (by rfl) ⟨394836, by rfl⟩ : syracuseStep 1052897 = 789673) B789673
theorem B2363633 : Blo 698317 2363633 := bstep (se 2 (by rfl) ⟨886362, by rfl⟩ : syracuseStep 2363633 = 1772725) B1772725
theorem B1773809 : Blo 698317 1773809 := bstep (se 2 (by rfl) ⟨665178, by rfl⟩ : syracuseStep 1773809 = 1330357) B1330357
theorem B1052915 : Blo 698317 1052915 := bstep (se 1 (by rfl) ⟨789686, by rfl⟩ : syracuseStep 1052915 = 1579373) B1579373
theorem B1184017 : Blo 698317 1184017 := bstep (se 2 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 1184017 = 888013) B888013
theorem B1052945 : Blo 698317 1052945 := bstep (se 2 (by rfl) ⟨394854, by rfl⟩ : syracuseStep 1052945 = 789709) B789709
theorem B1773859 : Blo 698317 1773859 := bstep (se 1 (by rfl) ⟨1330394, by rfl⟩ : syracuseStep 1773859 = 2660789) B2660789
theorem B1052963 : Blo 698317 1052963 := bstep (se 1 (by rfl) ⟨789722, by rfl⟩ : syracuseStep 1052963 = 1579445) B1579445
theorem B1184051 : Blo 698317 1184051 := bstep (se 1 (by rfl) ⟨888038, by rfl⟩ : syracuseStep 1184051 = 1776077) B1776077
theorem B1052993 : Blo 698317 1052993 := bstep (se 2 (by rfl) ⟨394872, by rfl⟩ : syracuseStep 1052993 = 789745) B789745
theorem B1053011 : Blo 698317 1053011 := bstep (se 1 (by rfl) ⟨789758, by rfl⟩ : syracuseStep 1053011 = 1579517) B1579517
theorem B1053041 : Blo 698317 1053041 := bstep (se 2 (by rfl) ⟨394890, by rfl⟩ : syracuseStep 1053041 = 789781) B789781
theorem B1053059 : Blo 698317 1053059 := bstep (se 1 (by rfl) ⟨789794, by rfl⟩ : syracuseStep 1053059 = 1579589) B1579589
theorem B1053089 : Blo 698317 1053089 := bstep (se 2 (by rfl) ⟨394908, by rfl⟩ : syracuseStep 1053089 = 789817) B789817
theorem B1774001 : Blo 698317 1774001 := bstep (se 2 (by rfl) ⟨665250, by rfl⟩ : syracuseStep 1774001 = 1330501) B1330501
theorem B1577393 : Blo 698317 1577393 := bstep (se 2 (by rfl) ⟨591522, by rfl⟩ : syracuseStep 1577393 = 1183045) B1183045
theorem B1184179 : Blo 698317 1184179 := bstep (se 1 (by rfl) ⟨888134, by rfl⟩ : syracuseStep 1184179 = 1776269) B1776269
theorem B1053107 : Blo 698317 1053107 := bstep (se 1 (by rfl) ⟨789830, by rfl⟩ : syracuseStep 1053107 = 1579661) B1579661
theorem B1577411 : Blo 698317 1577411 := bstep (se 1 (by rfl) ⟨1183058, by rfl⟩ : syracuseStep 1577411 = 2366117) B2366117
theorem B1053137 : Blo 698317 1053137 := bstep (se 2 (by rfl) ⟨394926, by rfl⟩ : syracuseStep 1053137 = 789853) B789853
theorem B1053155 : Blo 698317 1053155 := bstep (se 1 (by rfl) ⟨789866, by rfl⟩ : syracuseStep 1053155 = 1579733) B1579733
theorem B1053185 : Blo 698317 1053185 := bstep (se 2 (by rfl) ⟨394944, by rfl⟩ : syracuseStep 1053185 = 789889) B789889
theorem B1053203 : Blo 698317 1053203 := bstep (se 1 (by rfl) ⟨789902, by rfl⟩ : syracuseStep 1053203 = 1579805) B1579805
theorem B3543587 : Blo 698317 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B1053233 : Blo 698317 1053233 := bstep (se 2 (by rfl) ⟨394962, by rfl⟩ : syracuseStep 1053233 = 789925) B789925
theorem B1184321 : Blo 698317 1184321 := bstep (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) B888241
theorem B1053251 : Blo 698317 1053251 := bstep (se 1 (by rfl) ⟨789938, by rfl⟩ : syracuseStep 1053251 = 1579877) B1579877
theorem B1053281 : Blo 698317 1053281 := bstep (se 2 (by rfl) ⟨394980, by rfl⟩ : syracuseStep 1053281 = 789961) B789961
theorem B1053299 : Blo 698317 1053299 := bstep (se 1 (by rfl) ⟨789974, by rfl⟩ : syracuseStep 1053299 = 1579949) B1579949
theorem B1053329 : Blo 698317 1053329 := bstep (se 2 (by rfl) ⟨394998, by rfl⟩ : syracuseStep 1053329 = 789997) B789997
theorem B1053347 : Blo 698317 1053347 := bstep (se 1 (by rfl) ⟨790010, by rfl⟩ : syracuseStep 1053347 = 1580021) B1580021
theorem B1184449 : Blo 698317 1184449 := bstep (se 2 (by rfl) ⟨444168, by rfl⟩ : syracuseStep 1184449 = 888337) B888337
theorem B1053377 : Blo 698317 1053377 := bstep (se 2 (by rfl) ⟨395016, by rfl⟩ : syracuseStep 1053377 = 790033) B790033
theorem B1577681 : Blo 698317 1577681 := bstep (se 2 (by rfl) ⟨591630, by rfl⟩ : syracuseStep 1577681 = 1183261) B1183261
theorem B1053395 : Blo 698317 1053395 := bstep (se 1 (by rfl) ⟨790046, by rfl⟩ : syracuseStep 1053395 = 1580093) B1580093
theorem B1577699 : Blo 698317 1577699 := bstep (se 1 (by rfl) ⟨1183274, by rfl⟩ : syracuseStep 1577699 = 2366549) B2366549
theorem B1184483 : Blo 698317 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B1053425 : Blo 698317 1053425 := bstep (se 2 (by rfl) ⟨395034, by rfl⟩ : syracuseStep 1053425 = 790069) B790069
theorem B1053443 : Blo 698317 1053443 := bstep (se 1 (by rfl) ⟨790082, by rfl⟩ : syracuseStep 1053443 = 1580165) B1580165
theorem B2364173 : Blo 698317 2364173 := bstep (se 3 (by rfl) ⟨443282, by rfl⟩ : syracuseStep 2364173 = 886565) B886565
theorem B1053473 : Blo 698317 1053473 := bstep (se 2 (by rfl) ⟨395052, by rfl⟩ : syracuseStep 1053473 = 790105) B790105
theorem B2364227 : Blo 698317 2364227 := bstep (se 1 (by rfl) ⟨1773170, by rfl⟩ : syracuseStep 2364227 = 3546341) B3546341
theorem B1184611 : Blo 698317 1184611 := bstep (se 1 (by rfl) ⟨888458, by rfl⟩ : syracuseStep 1184611 = 1776917) B1776917
theorem B1577969 : Blo 698317 1577969 := bstep (se 2 (by rfl) ⟨591738, by rfl⟩ : syracuseStep 1577969 = 1183477) B1183477
theorem B1184753 : Blo 698317 1184753 := bstep (se 2 (by rfl) ⟨444282, by rfl⟩ : syracuseStep 1184753 = 888565) B888565
theorem B1577987 : Blo 698317 1577987 := bstep (se 1 (by rfl) ⟨1183490, by rfl⟩ : syracuseStep 1577987 = 2366981) B2366981
theorem B2364497 : Blo 698317 2364497 := bstep (se 2 (by rfl) ⟨886686, by rfl⟩ : syracuseStep 2364497 = 1773373) B1773373
theorem B1184881 : Blo 698317 1184881 := bstep (se 2 (by rfl) ⟨444330, by rfl⟩ : syracuseStep 1184881 = 888661) B888661
theorem B1184915 : Blo 698317 1184915 := bstep (se 1 (by rfl) ⟨888686, by rfl⟩ : syracuseStep 1184915 = 1777373) B1777373
theorem B1119395 : Blo 698317 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B2528497 : Blo 698317 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B1578257 : Blo 698317 1578257 := bstep (se 2 (by rfl) ⟨591846, by rfl⟩ : syracuseStep 1578257 = 1183693) B1183693
theorem B1185043 : Blo 698317 1185043 := bstep (se 1 (by rfl) ⟨888782, by rfl⟩ : syracuseStep 1185043 = 1777565) B1777565
theorem B1578275 : Blo 698317 1578275 := bstep (se 1 (by rfl) ⟨1183706, by rfl⟩ : syracuseStep 1578275 = 2367413) B2367413
theorem B3544397 : Blo 698317 3544397 := bstep (se 3 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 3544397 = 1329149) B1329149
theorem B1119619 : Blo 698317 1119619 := bstep (se 1 (by rfl) ⟨839714, by rfl⟩ : syracuseStep 1119619 = 1679429) B1679429
theorem B1774993 : Blo 698317 1774993 := bstep (se 2 (by rfl) ⟨665622, by rfl⟩ : syracuseStep 1774993 = 1331245) B1331245
theorem B1578545 : Blo 698317 1578545 := bstep (se 2 (by rfl) ⟨591954, by rfl⟩ : syracuseStep 1578545 = 1183909) B1183909
theorem B1578563 : Blo 698317 1578563 := bstep (se 1 (by rfl) ⟨1183922, by rfl⟩ : syracuseStep 1578563 = 2367845) B2367845
theorem B2365037 : Blo 698317 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B2692721 : Blo 698317 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B2135683 : Blo 698317 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B2365091 : Blo 698317 2365091 := bstep (se 1 (by rfl) ⟨1773818, by rfl⟩ : syracuseStep 2365091 = 3547637) B3547637
theorem B1775267 : Blo 698317 1775267 := bstep (se 1 (by rfl) ⟨1331450, by rfl⟩ : syracuseStep 1775267 = 2662901) B2662901
theorem B1578833 : Blo 698317 1578833 := bstep (se 2 (by rfl) ⟨592062, by rfl⟩ : syracuseStep 1578833 = 1184125) B1184125
theorem B1775459 : Blo 698317 1775459 := bstep (se 1 (by rfl) ⟨1331594, by rfl⟩ : syracuseStep 1775459 = 2663189) B2663189
theorem B1578851 : Blo 698317 1578851 := bstep (se 1 (by rfl) ⟨1184138, by rfl⟩ : syracuseStep 1578851 = 2368277) B2368277
theorem B2660273 : Blo 698317 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B2365361 : Blo 698317 2365361 := bstep (se 2 (by rfl) ⟨887010, by rfl⟩ : syracuseStep 2365361 = 1774021) B1774021
theorem B1153073 : Blo 698317 1153073 := bstep (se 2 (by rfl) ⟨432402, by rfl⟩ : syracuseStep 1153073 = 864805) B864805
theorem B8198213 : Blo 698317 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B1579121 : Blo 698317 1579121 := bstep (se 2 (by rfl) ⟨592170, by rfl⟩ : syracuseStep 1579121 = 1184341) B1184341
theorem B1579139 : Blo 698317 1579139 := bstep (se 1 (by rfl) ⟨1184354, by rfl⟩ : syracuseStep 1579139 = 2368709) B2368709
theorem B1120625 : Blo 698317 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B1579409 : Blo 698317 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B1579427 : Blo 698317 1579427 := bstep (se 1 (by rfl) ⟨1184570, by rfl⟩ : syracuseStep 1579427 = 2369141) B2369141
theorem B2365901 : Blo 698317 2365901 := bstep (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) B887213
theorem B4790755 : Blo 698317 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B2365955 : Blo 698317 2365955 := bstep (se 1 (by rfl) ⟨1774466, by rfl⟩ : syracuseStep 2365955 = 3548933) B3548933
theorem B1120817 : Blo 698317 1120817 := bstep (se 2 (by rfl) ⟨420306, by rfl⟩ : syracuseStep 1120817 = 840613) B840613
theorem B1579697 : Blo 698317 1579697 := bstep (se 2 (by rfl) ⟨592386, by rfl⟩ : syracuseStep 1579697 = 1184773) B1184773
theorem B1579715 : Blo 698317 1579715 := bstep (se 1 (by rfl) ⟨1184786, by rfl⟩ : syracuseStep 1579715 = 2369573) B2369573
theorem B2366225 : Blo 698317 2366225 := bstep (se 2 (by rfl) ⟨887334, by rfl⟩ : syracuseStep 2366225 = 1774669) B1774669
theorem B1776401 : Blo 698317 1776401 := bstep (se 2 (by rfl) ⟨666150, by rfl⟩ : syracuseStep 1776401 = 1332301) B1332301
theorem B1776451 : Blo 698317 1776451 := bstep (se 1 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 1776451 = 2664677) B2664677
theorem B1776593 : Blo 698317 1776593 := bstep (se 2 (by rfl) ⟨666222, by rfl⟩ : syracuseStep 1776593 = 1332445) B1332445
theorem B1579985 : Blo 698317 1579985 := bstep (se 2 (by rfl) ⟨592494, by rfl⟩ : syracuseStep 1579985 = 1184989) B1184989
theorem B1580003 : Blo 698317 1580003 := bstep (se 1 (by rfl) ⟨1185002, by rfl⟩ : syracuseStep 1580003 = 2370005) B2370005
theorem B8985653 : Blo 698317 8985653 := bstep (se 5 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 8985653 = 842405) B842405
theorem B1416305 : Blo 698317 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B4037795 : Blo 698317 4037795 := bstep (se 1 (by rfl) ⟨3028346, by rfl⟩ : syracuseStep 4037795 = 6056693) B6056693
theorem B2989219 : Blo 698317 2989219 := bstep (se 1 (by rfl) ⟨2241914, by rfl⟩ : syracuseStep 2989219 = 4483829) B4483829
theorem B2366765 : Blo 698317 2366765 := bstep (se 3 (by rfl) ⟨443768, by rfl⟩ : syracuseStep 2366765 = 887537) B887537
theorem B5053765 : Blo 698317 5053765 := bstep (se 4 (by rfl) ⟨473790, by rfl⟩ : syracuseStep 5053765 = 947581) B947581
theorem B2661731 : Blo 698317 2661731 := bstep (se 1 (by rfl) ⟨1996298, by rfl⟩ : syracuseStep 2661731 = 3992597) B3992597
theorem B2366819 : Blo 698317 2366819 := bstep (se 1 (by rfl) ⟨1775114, by rfl⟩ : syracuseStep 2366819 = 3550229) B3550229
theorem B2367089 : Blo 698317 2367089 := bstep (se 2 (by rfl) ⟨887658, by rfl⟩ : syracuseStep 2367089 = 1775317) B1775317
theorem B1777585 : Blo 698317 1777585 := bstep (se 2 (by rfl) ⟨666594, by rfl⟩ : syracuseStep 1777585 = 1333189) B1333189
theorem B7970885 : Blo 698317 7970885 := bstep (se 4 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 7970885 = 1494541) B1494541
theorem B1122419 : Blo 698317 1122419 := bstep (se 1 (by rfl) ⟨841814, by rfl⟩ : syracuseStep 1122419 = 1683629) B1683629
theorem B2367629 : Blo 698317 2367629 := bstep (se 3 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 2367629 = 887861) B887861
theorem B3547313 : Blo 698317 3547313 := bstep (se 2 (by rfl) ⟨1330242, by rfl⟩ : syracuseStep 3547313 = 2660485) B2660485
theorem B2367683 : Blo 698317 2367683 := bstep (se 1 (by rfl) ⟨1775762, by rfl⟩ : syracuseStep 2367683 = 3551525) B3551525
theorem B2433233 : Blo 698317 2433233 := bstep (se 2 (by rfl) ⟨912462, by rfl⟩ : syracuseStep 2433233 = 1824925) B1824925
theorem B2662733 : Blo 698317 2662733 := bstep (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) B998525
theorem B2990449 : Blo 698317 2990449 := bstep (se 2 (by rfl) ⟨1121418, by rfl⟩ : syracuseStep 2990449 = 2242837) B2242837
theorem B2367953 : Blo 698317 2367953 := bstep (se 2 (by rfl) ⟨887982, by rfl⟩ : syracuseStep 2367953 = 1775965) B1775965
theorem B1122803 : Blo 698317 1122803 := bstep (se 1 (by rfl) ⟨842102, by rfl⟩ : syracuseStep 1122803 = 1684205) B1684205
theorem B1122931 : Blo 698317 1122931 := bstep (se 1 (by rfl) ⟨842198, by rfl⟩ : syracuseStep 1122931 = 1684397) B1684397
theorem B4268785 : Blo 698317 4268785 := bstep (se 2 (by rfl) ⟨1600794, by rfl⟩ : syracuseStep 4268785 = 3201589) B3201589
theorem B1680227 : Blo 698317 1680227 := bstep (se 1 (by rfl) ⟨1260170, by rfl⟩ : syracuseStep 1680227 = 2520341) B2520341
theorem B2368493 : Blo 698317 2368493 := bstep (se 3 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 2368493 = 888185) B888185
theorem B2368547 : Blo 698317 2368547 := bstep (se 1 (by rfl) ⟨1776410, by rfl⟩ : syracuseStep 2368547 = 3552821) B3552821
theorem B2237507 : Blo 698317 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B2237635 : Blo 698317 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B2368817 : Blo 698317 2368817 := bstep (se 2 (by rfl) ⟨888306, by rfl⟩ : syracuseStep 2368817 = 1776613) B1776613
theorem B1123649 : Blo 698317 1123649 := bstep (se 2 (by rfl) ⟨421368, by rfl⟩ : syracuseStep 1123649 = 842737) B842737
theorem B2270531 : Blo 698317 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B1123841 : Blo 698317 1123841 := bstep (se 2 (by rfl) ⟨421440, by rfl⟩ : syracuseStep 1123841 = 842881) B842881
theorem B2237969 : Blo 698317 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B1680995 : Blo 698317 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B3548771 : Blo 698317 3548771 := bstep (se 1 (by rfl) ⟨2661578, by rfl⟩ : syracuseStep 3548771 = 5323157) B5323157
theorem B2369357 : Blo 698317 2369357 := bstep (se 3 (by rfl) ⟨444254, by rfl⟩ : syracuseStep 2369357 = 888509) B888509
theorem B2369411 : Blo 698317 2369411 := bstep (se 1 (by rfl) ⟨1777058, by rfl⟩ : syracuseStep 2369411 = 3554117) B3554117
theorem B2467757 : Blo 698317 2467757 := bstep (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) B925409
theorem B8071109 : Blo 698317 8071109 := bstep (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) B1513333
theorem B698323 : Blo 698317 698323 := bstep (se 1 (by rfl) ⟨523742, by rfl⟩ : syracuseStep 698323 = 1047485) B1047485
theorem B698339 : Blo 698317 698339 := bstep (se 1 (by rfl) ⟨523754, by rfl⟩ : syracuseStep 698339 = 1047509) B1047509
theorem B698355 : Blo 698317 698355 := bstep (se 1 (by rfl) ⟨523766, by rfl⟩ : syracuseStep 698355 = 1047533) B1047533
theorem B698371 : Blo 698317 698371 := bstep (se 1 (by rfl) ⟨523778, by rfl⟩ : syracuseStep 698371 = 1047557) B1047557
theorem B698387 : Blo 698317 698387 := bstep (se 1 (by rfl) ⟨523790, by rfl⟩ : syracuseStep 698387 = 1047581) B1047581
theorem B698403 : Blo 698317 698403 := bstep (se 1 (by rfl) ⟨523802, by rfl⟩ : syracuseStep 698403 = 1047605) B1047605
theorem B698419 : Blo 698317 698419 := bstep (se 1 (by rfl) ⟨523814, by rfl⟩ : syracuseStep 698419 = 1047629) B1047629
theorem B698435 : Blo 698317 698435 := bstep (se 1 (by rfl) ⟨523826, by rfl⟩ : syracuseStep 698435 = 1047653) B1047653
theorem B698451 : Blo 698317 698451 := bstep (se 1 (by rfl) ⟨523838, by rfl⟩ : syracuseStep 698451 = 1047677) B1047677
theorem B698467 : Blo 698317 698467 := bstep (se 1 (by rfl) ⟨523850, by rfl⟩ : syracuseStep 698467 = 1047701) B1047701
theorem B698483 : Blo 698317 698483 := bstep (se 1 (by rfl) ⟨523862, by rfl⟩ : syracuseStep 698483 = 1047725) B1047725
theorem B698499 : Blo 698317 698499 := bstep (se 1 (by rfl) ⟨523874, by rfl⟩ : syracuseStep 698499 = 1047749) B1047749
theorem B1681553 : Blo 698317 1681553 := bstep (se 2 (by rfl) ⟨630582, by rfl⟩ : syracuseStep 1681553 = 1261165) B1261165
theorem B2369681 : Blo 698317 2369681 := bstep (se 2 (by rfl) ⟨888630, by rfl⟩ : syracuseStep 2369681 = 1777261) B1777261
theorem B698515 : Blo 698317 698515 := bstep (se 1 (by rfl) ⟨523886, by rfl⟩ : syracuseStep 698515 = 1047773) B1047773
theorem B698531 : Blo 698317 698531 := bstep (se 1 (by rfl) ⟨523898, by rfl⟩ : syracuseStep 698531 = 1047797) B1047797
theorem B698547 : Blo 698317 698547 := bstep (se 1 (by rfl) ⟨523910, by rfl⟩ : syracuseStep 698547 = 1047821) B1047821
theorem B698563 : Blo 698317 698563 := bstep (se 1 (by rfl) ⟨523922, by rfl⟩ : syracuseStep 698563 = 1047845) B1047845
theorem B698579 : Blo 698317 698579 := bstep (se 1 (by rfl) ⟨523934, by rfl⟩ : syracuseStep 698579 = 1047869) B1047869
theorem B698595 : Blo 698317 698595 := bstep (se 1 (by rfl) ⟨523946, by rfl⟩ : syracuseStep 698595 = 1047893) B1047893
theorem B5056739 : Blo 698317 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B698611 : Blo 698317 698611 := bstep (se 1 (by rfl) ⟨523958, by rfl⟩ : syracuseStep 698611 = 1047917) B1047917
theorem B698627 : Blo 698317 698627 := bstep (se 1 (by rfl) ⟨523970, by rfl⟩ : syracuseStep 698627 = 1047941) B1047941
theorem B698643 : Blo 698317 698643 := bstep (se 1 (by rfl) ⟨523982, by rfl⟩ : syracuseStep 698643 = 1047965) B1047965
theorem B698659 : Blo 698317 698659 := bstep (se 1 (by rfl) ⟨523994, by rfl⟩ : syracuseStep 698659 = 1047989) B1047989
theorem B698675 : Blo 698317 698675 := bstep (se 1 (by rfl) ⟨524006, by rfl⟩ : syracuseStep 698675 = 1048013) B1048013
theorem B698691 : Blo 698317 698691 := bstep (se 1 (by rfl) ⟨524018, by rfl⟩ : syracuseStep 698691 = 1048037) B1048037
theorem B698707 : Blo 698317 698707 := bstep (se 1 (by rfl) ⟨524030, by rfl⟩ : syracuseStep 698707 = 1048061) B1048061
theorem B698723 : Blo 698317 698723 := bstep (se 1 (by rfl) ⟨524042, by rfl⟩ : syracuseStep 698723 = 1048085) B1048085
theorem B698739 : Blo 698317 698739 := bstep (se 1 (by rfl) ⟨524054, by rfl⟩ : syracuseStep 698739 = 1048109) B1048109
theorem B698755 : Blo 698317 698755 := bstep (se 1 (by rfl) ⟨524066, by rfl⟩ : syracuseStep 698755 = 1048133) B1048133
theorem B3549581 : Blo 698317 3549581 := bstep (se 3 (by rfl) ⟨665546, by rfl⟩ : syracuseStep 3549581 = 1331093) B1331093
theorem B2664845 : Blo 698317 2664845 := bstep (se 3 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 2664845 = 999317) B999317
theorem B698771 : Blo 698317 698771 := bstep (se 1 (by rfl) ⟨524078, by rfl⟩ : syracuseStep 698771 = 1048157) B1048157
theorem B698787 : Blo 698317 698787 := bstep (se 1 (by rfl) ⟨524090, by rfl⟩ : syracuseStep 698787 = 1048181) B1048181
theorem B698803 : Blo 698317 698803 := bstep (se 1 (by rfl) ⟨524102, by rfl⟩ : syracuseStep 698803 = 1048205) B1048205
theorem B698819 : Blo 698317 698819 := bstep (se 1 (by rfl) ⟨524114, by rfl⟩ : syracuseStep 698819 = 1048229) B1048229
theorem B698835 : Blo 698317 698835 := bstep (se 1 (by rfl) ⟨524126, by rfl⟩ : syracuseStep 698835 = 1048253) B1048253
theorem B698851 : Blo 698317 698851 := bstep (se 1 (by rfl) ⟨524138, by rfl⟩ : syracuseStep 698851 = 1048277) B1048277
theorem B16394723 : Blo 698317 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B698867 : Blo 698317 698867 := bstep (se 1 (by rfl) ⟨524150, by rfl⟩ : syracuseStep 698867 = 1048301) B1048301
theorem B698883 : Blo 698317 698883 := bstep (se 1 (by rfl) ⟨524162, by rfl⟩ : syracuseStep 698883 = 1048325) B1048325
theorem B1681937 : Blo 698317 1681937 := bstep (se 2 (by rfl) ⟨630726, by rfl⟩ : syracuseStep 1681937 = 1261453) B1261453
theorem B698899 : Blo 698317 698899 := bstep (se 1 (by rfl) ⟨524174, by rfl⟩ : syracuseStep 698899 = 1048349) B1048349
theorem B698915 : Blo 698317 698915 := bstep (se 1 (by rfl) ⟨524186, by rfl⟩ : syracuseStep 698915 = 1048373) B1048373
theorem B698931 : Blo 698317 698931 := bstep (se 1 (by rfl) ⟨524198, by rfl⟩ : syracuseStep 698931 = 1048397) B1048397
theorem B698947 : Blo 698317 698947 := bstep (se 1 (by rfl) ⟨524210, by rfl⟩ : syracuseStep 698947 = 1048421) B1048421
theorem B698963 : Blo 698317 698963 := bstep (se 1 (by rfl) ⟨524222, by rfl⟩ : syracuseStep 698963 = 1048445) B1048445
theorem B698979 : Blo 698317 698979 := bstep (se 1 (by rfl) ⟨524234, by rfl⟩ : syracuseStep 698979 = 1048469) B1048469
theorem B698995 : Blo 698317 698995 := bstep (se 1 (by rfl) ⟨524246, by rfl⟩ : syracuseStep 698995 = 1048493) B1048493
theorem B699011 : Blo 698317 699011 := bstep (se 1 (by rfl) ⟨524258, by rfl⟩ : syracuseStep 699011 = 1048517) B1048517
theorem B1682051 : Blo 698317 1682051 := bstep (se 1 (by rfl) ⟨1261538, by rfl⟩ : syracuseStep 1682051 = 2523077) B2523077
theorem B699027 : Blo 698317 699027 := bstep (se 1 (by rfl) ⟨524270, by rfl⟩ : syracuseStep 699027 = 1048541) B1048541
theorem B699043 : Blo 698317 699043 := bstep (se 1 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 699043 = 1048565) B1048565
theorem B2370221 : Blo 698317 2370221 := bstep (se 3 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 2370221 = 888833) B888833
theorem B699059 : Blo 698317 699059 := bstep (se 1 (by rfl) ⟨524294, by rfl⟩ : syracuseStep 699059 = 1048589) B1048589
theorem B699075 : Blo 698317 699075 := bstep (se 1 (by rfl) ⟨524306, by rfl⟩ : syracuseStep 699075 = 1048613) B1048613
theorem B699091 : Blo 698317 699091 := bstep (se 1 (by rfl) ⟨524318, by rfl⟩ : syracuseStep 699091 = 1048637) B1048637
theorem B699107 : Blo 698317 699107 := bstep (se 1 (by rfl) ⟨524330, by rfl⟩ : syracuseStep 699107 = 1048661) B1048661
theorem B2370275 : Blo 698317 2370275 := bstep (se 1 (by rfl) ⟨1777706, by rfl⟩ : syracuseStep 2370275 = 3555413) B3555413
theorem B699123 : Blo 698317 699123 := bstep (se 1 (by rfl) ⟨524342, by rfl⟩ : syracuseStep 699123 = 1048685) B1048685
theorem B699139 : Blo 698317 699139 := bstep (se 1 (by rfl) ⟨524354, by rfl⟩ : syracuseStep 699139 = 1048709) B1048709
theorem B699155 : Blo 698317 699155 := bstep (se 1 (by rfl) ⟨524366, by rfl⟩ : syracuseStep 699155 = 1048733) B1048733
theorem B36285205 : Blo 698317 36285205 := bstep (se 6 (by rfl) ⟨850434, by rfl⟩ : syracuseStep 36285205 = 1700869) B1700869
theorem B699171 : Blo 698317 699171 := bstep (se 1 (by rfl) ⟨524378, by rfl⟩ : syracuseStep 699171 = 1048757) B1048757
theorem B1682225 : Blo 698317 1682225 := bstep (se 2 (by rfl) ⟨630834, by rfl⟩ : syracuseStep 1682225 = 1261669) B1261669
theorem B699187 : Blo 698317 699187 := bstep (se 1 (by rfl) ⟨524390, by rfl⟩ : syracuseStep 699187 = 1048781) B1048781
theorem B699203 : Blo 698317 699203 := bstep (se 1 (by rfl) ⟨524402, by rfl⟩ : syracuseStep 699203 = 1048805) B1048805
theorem B699219 : Blo 698317 699219 := bstep (se 1 (by rfl) ⟨524414, by rfl⟩ : syracuseStep 699219 = 1048829) B1048829
theorem B699235 : Blo 698317 699235 := bstep (se 1 (by rfl) ⟨524426, by rfl⟩ : syracuseStep 699235 = 1048853) B1048853
theorem B699251 : Blo 698317 699251 := bstep (se 1 (by rfl) ⟨524438, by rfl⟩ : syracuseStep 699251 = 1048877) B1048877
theorem B699267 : Blo 698317 699267 := bstep (se 1 (by rfl) ⟨524450, by rfl⟩ : syracuseStep 699267 = 1048901) B1048901
theorem B699283 : Blo 698317 699283 := bstep (se 1 (by rfl) ⟨524462, by rfl⟩ : syracuseStep 699283 = 1048925) B1048925
theorem B699299 : Blo 698317 699299 := bstep (se 1 (by rfl) ⟨524474, by rfl⟩ : syracuseStep 699299 = 1048949) B1048949
theorem B699315 : Blo 698317 699315 := bstep (se 1 (by rfl) ⟨524486, by rfl⟩ : syracuseStep 699315 = 1048973) B1048973
theorem B699331 : Blo 698317 699331 := bstep (se 1 (by rfl) ⟨524498, by rfl⟩ : syracuseStep 699331 = 1048997) B1048997
theorem B3845069 : Blo 698317 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B699347 : Blo 698317 699347 := bstep (se 1 (by rfl) ⟨524510, by rfl⟩ : syracuseStep 699347 = 1049021) B1049021
theorem B699363 : Blo 698317 699363 := bstep (se 1 (by rfl) ⟨524522, by rfl⟩ : syracuseStep 699363 = 1049045) B1049045
theorem B699379 : Blo 698317 699379 := bstep (se 1 (by rfl) ⟨524534, by rfl⟩ : syracuseStep 699379 = 1049069) B1049069
theorem B699395 : Blo 698317 699395 := bstep (se 1 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 699395 = 1049093) B1049093
theorem B699411 : Blo 698317 699411 := bstep (se 1 (by rfl) ⟨524558, by rfl⟩ : syracuseStep 699411 = 1049117) B1049117
theorem B699427 : Blo 698317 699427 := bstep (se 1 (by rfl) ⟨524570, by rfl⟩ : syracuseStep 699427 = 1049141) B1049141
theorem B699443 : Blo 698317 699443 := bstep (se 1 (by rfl) ⟨524582, by rfl⟩ : syracuseStep 699443 = 1049165) B1049165
theorem B11971637 : Blo 698317 11971637 := bstep (se 5 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 11971637 = 1122341) B1122341
theorem B699459 : Blo 698317 699459 := bstep (se 1 (by rfl) ⟨524594, by rfl⟩ : syracuseStep 699459 = 1049189) B1049189
theorem B699475 : Blo 698317 699475 := bstep (se 1 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 699475 = 1049213) B1049213
theorem B699491 : Blo 698317 699491 := bstep (se 1 (by rfl) ⟨524618, by rfl⟩ : syracuseStep 699491 = 1049237) B1049237
theorem B699507 : Blo 698317 699507 := bstep (se 1 (by rfl) ⟨524630, by rfl⟩ : syracuseStep 699507 = 1049261) B1049261
theorem B699523 : Blo 698317 699523 := bstep (se 1 (by rfl) ⟨524642, by rfl⟩ : syracuseStep 699523 = 1049285) B1049285
theorem B699539 : Blo 698317 699539 := bstep (se 1 (by rfl) ⟨524654, by rfl⟩ : syracuseStep 699539 = 1049309) B1049309
theorem B699555 : Blo 698317 699555 := bstep (se 1 (by rfl) ⟨524666, by rfl⟩ : syracuseStep 699555 = 1049333) B1049333
theorem B2665649 : Blo 698317 2665649 := bstep (se 2 (by rfl) ⟨999618, by rfl⟩ : syracuseStep 2665649 = 1999237) B1999237
theorem B699571 : Blo 698317 699571 := bstep (se 1 (by rfl) ⟨524678, by rfl⟩ : syracuseStep 699571 = 1049357) B1049357
theorem B699587 : Blo 698317 699587 := bstep (se 1 (by rfl) ⟨524690, by rfl⟩ : syracuseStep 699587 = 1049381) B1049381
theorem B699603 : Blo 698317 699603 := bstep (se 1 (by rfl) ⟨524702, by rfl⟩ : syracuseStep 699603 = 1049405) B1049405
theorem B699619 : Blo 698317 699619 := bstep (se 1 (by rfl) ⟨524714, by rfl⟩ : syracuseStep 699619 = 1049429) B1049429
theorem B699635 : Blo 698317 699635 := bstep (se 1 (by rfl) ⟨524726, by rfl⟩ : syracuseStep 699635 = 1049453) B1049453
theorem B699651 : Blo 698317 699651 := bstep (se 1 (by rfl) ⟨524738, by rfl⟩ : syracuseStep 699651 = 1049477) B1049477
theorem B699667 : Blo 698317 699667 := bstep (se 1 (by rfl) ⟨524750, by rfl⟩ : syracuseStep 699667 = 1049501) B1049501
theorem B699683 : Blo 698317 699683 := bstep (se 1 (by rfl) ⟨524762, by rfl⟩ : syracuseStep 699683 = 1049525) B1049525
theorem B699699 : Blo 698317 699699 := bstep (se 1 (by rfl) ⟨524774, by rfl⟩ : syracuseStep 699699 = 1049549) B1049549
theorem B699715 : Blo 698317 699715 := bstep (se 1 (by rfl) ⟨524786, by rfl⟩ : syracuseStep 699715 = 1049573) B1049573
theorem B699731 : Blo 698317 699731 := bstep (se 1 (by rfl) ⟨524798, by rfl⟩ : syracuseStep 699731 = 1049597) B1049597
theorem B699747 : Blo 698317 699747 := bstep (se 1 (by rfl) ⟨524810, by rfl⟩ : syracuseStep 699747 = 1049621) B1049621
theorem B994675 : Blo 698317 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B699763 : Blo 698317 699763 := bstep (se 1 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 699763 = 1049645) B1049645
theorem B699779 : Blo 698317 699779 := bstep (se 1 (by rfl) ⟨524834, by rfl⟩ : syracuseStep 699779 = 1049669) B1049669
theorem B699795 : Blo 698317 699795 := bstep (se 1 (by rfl) ⟨524846, by rfl⟩ : syracuseStep 699795 = 1049693) B1049693
theorem B699811 : Blo 698317 699811 := bstep (se 1 (by rfl) ⟨524858, by rfl⟩ : syracuseStep 699811 = 1049717) B1049717
theorem B699827 : Blo 698317 699827 := bstep (se 1 (by rfl) ⟨524870, by rfl⟩ : syracuseStep 699827 = 1049741) B1049741
theorem B699843 : Blo 698317 699843 := bstep (se 1 (by rfl) ⟨524882, by rfl⟩ : syracuseStep 699843 = 1049765) B1049765
theorem B699859 : Blo 698317 699859 := bstep (se 1 (by rfl) ⟨524894, by rfl⟩ : syracuseStep 699859 = 1049789) B1049789
theorem B699875 : Blo 698317 699875 := bstep (se 1 (by rfl) ⟨524906, by rfl⟩ : syracuseStep 699875 = 1049813) B1049813
theorem B699891 : Blo 698317 699891 := bstep (se 1 (by rfl) ⟨524918, by rfl⟩ : syracuseStep 699891 = 1049837) B1049837
theorem B699907 : Blo 698317 699907 := bstep (se 1 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 699907 = 1049861) B1049861
theorem B699923 : Blo 698317 699923 := bstep (se 1 (by rfl) ⟨524942, by rfl⟩ : syracuseStep 699923 = 1049885) B1049885
theorem B699939 : Blo 698317 699939 := bstep (se 1 (by rfl) ⟨524954, by rfl⟩ : syracuseStep 699939 = 1049909) B1049909
theorem B699955 : Blo 698317 699955 := bstep (se 1 (by rfl) ⟨524966, by rfl⟩ : syracuseStep 699955 = 1049933) B1049933
theorem B699971 : Blo 698317 699971 := bstep (se 1 (by rfl) ⟨524978, by rfl⟩ : syracuseStep 699971 = 1049957) B1049957
theorem B699987 : Blo 698317 699987 := bstep (se 1 (by rfl) ⟨524990, by rfl⟩ : syracuseStep 699987 = 1049981) B1049981
theorem B700003 : Blo 698317 700003 := bstep (se 1 (by rfl) ⟨525002, by rfl⟩ : syracuseStep 700003 = 1050005) B1050005
theorem B700019 : Blo 698317 700019 := bstep (se 1 (by rfl) ⟨525014, by rfl⟩ : syracuseStep 700019 = 1050029) B1050029
theorem B700035 : Blo 698317 700035 := bstep (se 1 (by rfl) ⟨525026, by rfl⟩ : syracuseStep 700035 = 1050053) B1050053
theorem B700051 : Blo 698317 700051 := bstep (se 1 (by rfl) ⟨525038, by rfl⟩ : syracuseStep 700051 = 1050077) B1050077
theorem B700067 : Blo 698317 700067 := bstep (se 1 (by rfl) ⟨525050, by rfl⟩ : syracuseStep 700067 = 1050101) B1050101
theorem B700083 : Blo 698317 700083 := bstep (se 1 (by rfl) ⟨525062, by rfl⟩ : syracuseStep 700083 = 1050125) B1050125
theorem B700099 : Blo 698317 700099 := bstep (se 1 (by rfl) ⟨525074, by rfl⟩ : syracuseStep 700099 = 1050149) B1050149
theorem B700115 : Blo 698317 700115 := bstep (se 1 (by rfl) ⟨525086, by rfl⟩ : syracuseStep 700115 = 1050173) B1050173
theorem B700131 : Blo 698317 700131 := bstep (se 1 (by rfl) ⟨525098, by rfl⟩ : syracuseStep 700131 = 1050197) B1050197
theorem B700147 : Blo 698317 700147 := bstep (se 1 (by rfl) ⟨525110, by rfl⟩ : syracuseStep 700147 = 1050221) B1050221
theorem B700163 : Blo 698317 700163 := bstep (se 1 (by rfl) ⟨525122, by rfl⟩ : syracuseStep 700163 = 1050245) B1050245
theorem B700179 : Blo 698317 700179 := bstep (se 1 (by rfl) ⟨525134, by rfl⟩ : syracuseStep 700179 = 1050269) B1050269
theorem B700195 : Blo 698317 700195 := bstep (se 1 (by rfl) ⟨525146, by rfl⟩ : syracuseStep 700195 = 1050293) B1050293
theorem B700211 : Blo 698317 700211 := bstep (se 1 (by rfl) ⟨525158, by rfl⟩ : syracuseStep 700211 = 1050317) B1050317
theorem B1748803 : Blo 698317 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B700227 : Blo 698317 700227 := bstep (se 1 (by rfl) ⟨525170, by rfl⟩ : syracuseStep 700227 = 1050341) B1050341
theorem B2666317 : Blo 698317 2666317 := bstep (se 3 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 2666317 = 999869) B999869
theorem B700243 : Blo 698317 700243 := bstep (se 1 (by rfl) ⟨525182, by rfl⟩ : syracuseStep 700243 = 1050365) B1050365
theorem B700259 : Blo 698317 700259 := bstep (se 1 (by rfl) ⟨525194, by rfl⟩ : syracuseStep 700259 = 1050389) B1050389
theorem B700275 : Blo 698317 700275 := bstep (se 1 (by rfl) ⟨525206, by rfl⟩ : syracuseStep 700275 = 1050413) B1050413
theorem B700291 : Blo 698317 700291 := bstep (se 1 (by rfl) ⟨525218, by rfl⟩ : syracuseStep 700291 = 1050437) B1050437
theorem B4042637 : Blo 698317 4042637 := bstep (se 3 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 4042637 = 1515989) B1515989
theorem B700307 : Blo 698317 700307 := bstep (se 1 (by rfl) ⟨525230, by rfl⟩ : syracuseStep 700307 = 1050461) B1050461
theorem B700323 : Blo 698317 700323 := bstep (se 1 (by rfl) ⟨525242, by rfl⟩ : syracuseStep 700323 = 1050485) B1050485
theorem B700339 : Blo 698317 700339 := bstep (se 1 (by rfl) ⟨525254, by rfl⟩ : syracuseStep 700339 = 1050509) B1050509
theorem B700355 : Blo 698317 700355 := bstep (se 1 (by rfl) ⟨525266, by rfl⟩ : syracuseStep 700355 = 1050533) B1050533
theorem B700371 : Blo 698317 700371 := bstep (se 1 (by rfl) ⟨525278, by rfl⟩ : syracuseStep 700371 = 1050557) B1050557
theorem B700387 : Blo 698317 700387 := bstep (se 1 (by rfl) ⟨525290, by rfl⟩ : syracuseStep 700387 = 1050581) B1050581
theorem B700403 : Blo 698317 700403 := bstep (se 1 (by rfl) ⟨525302, by rfl⟩ : syracuseStep 700403 = 1050605) B1050605
theorem B700419 : Blo 698317 700419 := bstep (se 1 (by rfl) ⟨525314, by rfl⟩ : syracuseStep 700419 = 1050629) B1050629
theorem B700435 : Blo 698317 700435 := bstep (se 1 (by rfl) ⟨525326, by rfl⟩ : syracuseStep 700435 = 1050653) B1050653
theorem B700451 : Blo 698317 700451 := bstep (se 1 (by rfl) ⟨525338, by rfl⟩ : syracuseStep 700451 = 1050677) B1050677
theorem B700467 : Blo 698317 700467 := bstep (se 1 (by rfl) ⟨525350, by rfl⟩ : syracuseStep 700467 = 1050701) B1050701
theorem B700483 : Blo 698317 700483 := bstep (se 1 (by rfl) ⟨525362, by rfl⟩ : syracuseStep 700483 = 1050725) B1050725
theorem B700499 : Blo 698317 700499 := bstep (se 1 (by rfl) ⟨525374, by rfl⟩ : syracuseStep 700499 = 1050749) B1050749
theorem B700515 : Blo 698317 700515 := bstep (se 1 (by rfl) ⟨525386, by rfl⟩ : syracuseStep 700515 = 1050773) B1050773
theorem B700531 : Blo 698317 700531 := bstep (se 1 (by rfl) ⟨525398, by rfl⟩ : syracuseStep 700531 = 1050797) B1050797
theorem B700547 : Blo 698317 700547 := bstep (se 1 (by rfl) ⟨525410, by rfl⟩ : syracuseStep 700547 = 1050821) B1050821
theorem B700563 : Blo 698317 700563 := bstep (se 1 (by rfl) ⟨525422, by rfl⟩ : syracuseStep 700563 = 1050845) B1050845
theorem B700579 : Blo 698317 700579 := bstep (se 1 (by rfl) ⟨525434, by rfl⟩ : syracuseStep 700579 = 1050869) B1050869
theorem B700595 : Blo 698317 700595 := bstep (se 1 (by rfl) ⟨525446, by rfl⟩ : syracuseStep 700595 = 1050893) B1050893
theorem B700611 : Blo 698317 700611 := bstep (se 1 (by rfl) ⟨525458, by rfl⟩ : syracuseStep 700611 = 1050917) B1050917
theorem B700627 : Blo 698317 700627 := bstep (se 1 (by rfl) ⟨525470, by rfl⟩ : syracuseStep 700627 = 1050941) B1050941
theorem B700643 : Blo 698317 700643 := bstep (se 1 (by rfl) ⟨525482, by rfl⟩ : syracuseStep 700643 = 1050965) B1050965
theorem B700659 : Blo 698317 700659 := bstep (se 1 (by rfl) ⟨525494, by rfl⟩ : syracuseStep 700659 = 1050989) B1050989
theorem B700675 : Blo 698317 700675 := bstep (se 1 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 700675 = 1051013) B1051013
theorem B700691 : Blo 698317 700691 := bstep (se 1 (by rfl) ⟨525518, by rfl⟩ : syracuseStep 700691 = 1051037) B1051037
theorem B700707 : Blo 698317 700707 := bstep (se 1 (by rfl) ⟨525530, by rfl⟩ : syracuseStep 700707 = 1051061) B1051061
theorem B700723 : Blo 698317 700723 := bstep (se 1 (by rfl) ⟨525542, by rfl⟩ : syracuseStep 700723 = 1051085) B1051085
theorem B700739 : Blo 698317 700739 := bstep (se 1 (by rfl) ⟨525554, by rfl⟩ : syracuseStep 700739 = 1051109) B1051109
theorem B700755 : Blo 698317 700755 := bstep (se 1 (by rfl) ⟨525566, by rfl⟩ : syracuseStep 700755 = 1051133) B1051133
theorem B700771 : Blo 698317 700771 := bstep (se 1 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 700771 = 1051157) B1051157
theorem B3977585 : Blo 698317 3977585 := bstep (se 2 (by rfl) ⟨1491594, by rfl⟩ : syracuseStep 3977585 = 2983189) B2983189
theorem B700787 : Blo 698317 700787 := bstep (se 1 (by rfl) ⟨525590, by rfl⟩ : syracuseStep 700787 = 1051181) B1051181
theorem B700803 : Blo 698317 700803 := bstep (se 1 (by rfl) ⟨525602, by rfl⟩ : syracuseStep 700803 = 1051205) B1051205
theorem B700819 : Blo 698317 700819 := bstep (se 1 (by rfl) ⟨525614, by rfl⟩ : syracuseStep 700819 = 1051229) B1051229
theorem B700835 : Blo 698317 700835 := bstep (se 1 (by rfl) ⟨525626, by rfl⟩ : syracuseStep 700835 = 1051253) B1051253
theorem B2240941 : Blo 698317 2240941 := bstep (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) B840353
theorem B700851 : Blo 698317 700851 := bstep (se 1 (by rfl) ⟨525638, by rfl⟩ : syracuseStep 700851 = 1051277) B1051277
theorem B700867 : Blo 698317 700867 := bstep (se 1 (by rfl) ⟨525650, by rfl⟩ : syracuseStep 700867 = 1051301) B1051301
theorem B700883 : Blo 698317 700883 := bstep (se 1 (by rfl) ⟨525662, by rfl⟩ : syracuseStep 700883 = 1051325) B1051325
theorem B995809 : Blo 698317 995809 := bstep (se 2 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 995809 = 746857) B746857
theorem B700899 : Blo 698317 700899 := bstep (se 1 (by rfl) ⟨525674, by rfl⟩ : syracuseStep 700899 = 1051349) B1051349
theorem B700915 : Blo 698317 700915 := bstep (se 1 (by rfl) ⟨525686, by rfl⟩ : syracuseStep 700915 = 1051373) B1051373
theorem B700931 : Blo 698317 700931 := bstep (se 1 (by rfl) ⟨525698, by rfl⟩ : syracuseStep 700931 = 1051397) B1051397
theorem B700947 : Blo 698317 700947 := bstep (se 1 (by rfl) ⟨525710, by rfl⟩ : syracuseStep 700947 = 1051421) B1051421
theorem B700963 : Blo 698317 700963 := bstep (se 1 (by rfl) ⟨525722, by rfl⟩ : syracuseStep 700963 = 1051445) B1051445
theorem B700979 : Blo 698317 700979 := bstep (se 1 (by rfl) ⟨525734, by rfl⟩ : syracuseStep 700979 = 1051469) B1051469
theorem B995905 : Blo 698317 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B700995 : Blo 698317 700995 := bstep (se 1 (by rfl) ⟨525746, by rfl⟩ : syracuseStep 700995 = 1051493) B1051493
theorem B1421891 : Blo 698317 1421891 := bstep (se 1 (by rfl) ⟨1066418, by rfl⟩ : syracuseStep 1421891 = 2132837) B2132837
theorem B701011 : Blo 698317 701011 := bstep (se 1 (by rfl) ⟨525758, by rfl⟩ : syracuseStep 701011 = 1051517) B1051517
theorem B701027 : Blo 698317 701027 := bstep (se 1 (by rfl) ⟨525770, by rfl⟩ : syracuseStep 701027 = 1051541) B1051541
theorem B20165233 : Blo 698317 20165233 := bstep (se 2 (by rfl) ⟨7561962, by rfl⟩ : syracuseStep 20165233 = 15123925) B15123925
theorem B701043 : Blo 698317 701043 := bstep (se 1 (by rfl) ⟨525782, by rfl⟩ : syracuseStep 701043 = 1051565) B1051565
theorem B701059 : Blo 698317 701059 := bstep (se 1 (by rfl) ⟨525794, by rfl⟩ : syracuseStep 701059 = 1051589) B1051589
theorem B2044561 : Blo 698317 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B701075 : Blo 698317 701075 := bstep (se 1 (by rfl) ⟨525806, by rfl⟩ : syracuseStep 701075 = 1051613) B1051613
theorem B701091 : Blo 698317 701091 := bstep (se 1 (by rfl) ⟨525818, by rfl⟩ : syracuseStep 701091 = 1051637) B1051637
theorem B2241197 : Blo 698317 2241197 := bstep (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) B840449
theorem B701107 : Blo 698317 701107 := bstep (se 1 (by rfl) ⟨525830, by rfl⟩ : syracuseStep 701107 = 1051661) B1051661
theorem B701123 : Blo 698317 701123 := bstep (se 1 (by rfl) ⟨525842, by rfl⟩ : syracuseStep 701123 = 1051685) B1051685
theorem B2994893 : Blo 698317 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B701139 : Blo 698317 701139 := bstep (se 1 (by rfl) ⟨525854, by rfl⟩ : syracuseStep 701139 = 1051709) B1051709
theorem B701155 : Blo 698317 701155 := bstep (se 1 (by rfl) ⟨525866, by rfl⟩ : syracuseStep 701155 = 1051733) B1051733
theorem B701171 : Blo 698317 701171 := bstep (se 1 (by rfl) ⟨525878, by rfl⟩ : syracuseStep 701171 = 1051757) B1051757
theorem B701187 : Blo 698317 701187 := bstep (se 1 (by rfl) ⟨525890, by rfl⟩ : syracuseStep 701187 = 1051781) B1051781
theorem B701203 : Blo 698317 701203 := bstep (se 1 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 701203 = 1051805) B1051805
theorem B701219 : Blo 698317 701219 := bstep (se 1 (by rfl) ⟨525914, by rfl⟩ : syracuseStep 701219 = 1051829) B1051829
theorem B701235 : Blo 698317 701235 := bstep (se 1 (by rfl) ⟨525926, by rfl⟩ : syracuseStep 701235 = 1051853) B1051853
theorem B701251 : Blo 698317 701251 := bstep (se 1 (by rfl) ⟨525938, by rfl⟩ : syracuseStep 701251 = 1051877) B1051877
theorem B701267 : Blo 698317 701267 := bstep (se 1 (by rfl) ⟨525950, by rfl⟩ : syracuseStep 701267 = 1051901) B1051901
theorem B701283 : Blo 698317 701283 := bstep (se 1 (by rfl) ⟨525962, by rfl⟩ : syracuseStep 701283 = 1051925) B1051925
theorem B3191665 : Blo 698317 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B10236785 : Blo 698317 10236785 := bstep (se 2 (by rfl) ⟨3838794, by rfl⟩ : syracuseStep 10236785 = 7677589) B7677589
theorem B701299 : Blo 698317 701299 := bstep (se 1 (by rfl) ⟨525974, by rfl⟩ : syracuseStep 701299 = 1051949) B1051949
theorem B701315 : Blo 698317 701315 := bstep (se 1 (by rfl) ⟨525986, by rfl⟩ : syracuseStep 701315 = 1051973) B1051973
theorem B26227597 : Blo 698317 26227597 := bstep (se 3 (by rfl) ⟨4917674, by rfl⟩ : syracuseStep 26227597 = 9835349) B9835349
theorem B701331 : Blo 698317 701331 := bstep (se 1 (by rfl) ⟨525998, by rfl⟩ : syracuseStep 701331 = 1051997) B1051997
theorem B701347 : Blo 698317 701347 := bstep (se 1 (by rfl) ⟨526010, by rfl⟩ : syracuseStep 701347 = 1052021) B1052021
theorem B701363 : Blo 698317 701363 := bstep (se 1 (by rfl) ⟨526022, by rfl⟩ : syracuseStep 701363 = 1052045) B1052045
theorem B701379 : Blo 698317 701379 := bstep (se 1 (by rfl) ⟨526034, by rfl⟩ : syracuseStep 701379 = 1052069) B1052069
theorem B701395 : Blo 698317 701395 := bstep (se 1 (by rfl) ⟨526046, by rfl⟩ : syracuseStep 701395 = 1052093) B1052093
theorem B5321699 : Blo 698317 5321699 := bstep (se 1 (by rfl) ⟨3991274, by rfl⟩ : syracuseStep 5321699 = 7982549) B7982549
theorem B701411 : Blo 698317 701411 := bstep (se 1 (by rfl) ⟨526058, by rfl⟩ : syracuseStep 701411 = 1052117) B1052117
theorem B701427 : Blo 698317 701427 := bstep (se 1 (by rfl) ⟨526070, by rfl⟩ : syracuseStep 701427 = 1052141) B1052141
theorem B701443 : Blo 698317 701443 := bstep (se 1 (by rfl) ⟨526082, by rfl⟩ : syracuseStep 701443 = 1052165) B1052165
theorem B701459 : Blo 698317 701459 := bstep (se 1 (by rfl) ⟨526094, by rfl⟩ : syracuseStep 701459 = 1052189) B1052189
theorem B701475 : Blo 698317 701475 := bstep (se 1 (by rfl) ⟨526106, by rfl⟩ : syracuseStep 701475 = 1052213) B1052213
theorem B996401 : Blo 698317 996401 := bstep (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) B747301
theorem B701491 : Blo 698317 701491 := bstep (se 1 (by rfl) ⟨526118, by rfl⟩ : syracuseStep 701491 = 1052237) B1052237
theorem B701507 : Blo 698317 701507 := bstep (se 1 (by rfl) ⟨526130, by rfl⟩ : syracuseStep 701507 = 1052261) B1052261
theorem B8959045 : Blo 698317 8959045 := bstep (se 4 (by rfl) ⟨839910, by rfl⟩ : syracuseStep 8959045 = 1679821) B1679821
theorem B701523 : Blo 698317 701523 := bstep (se 1 (by rfl) ⟨526142, by rfl⟩ : syracuseStep 701523 = 1052285) B1052285
theorem B701539 : Blo 698317 701539 := bstep (se 1 (by rfl) ⟨526154, by rfl⟩ : syracuseStep 701539 = 1052309) B1052309
theorem B701555 : Blo 698317 701555 := bstep (se 1 (by rfl) ⟨526166, by rfl⟩ : syracuseStep 701555 = 1052333) B1052333
theorem B701571 : Blo 698317 701571 := bstep (se 1 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 701571 = 1052357) B1052357
theorem B701587 : Blo 698317 701587 := bstep (se 1 (by rfl) ⟨526190, by rfl⟩ : syracuseStep 701587 = 1052381) B1052381
theorem B701603 : Blo 698317 701603 := bstep (se 1 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 701603 = 1052405) B1052405
theorem B701619 : Blo 698317 701619 := bstep (se 1 (by rfl) ⟨526214, by rfl⟩ : syracuseStep 701619 = 1052429) B1052429
theorem B701635 : Blo 698317 701635 := bstep (se 1 (by rfl) ⟨526226, by rfl⟩ : syracuseStep 701635 = 1052453) B1052453
theorem B3781829 : Blo 698317 3781829 := bstep (se 4 (by rfl) ⟨354546, by rfl⟩ : syracuseStep 3781829 = 709093) B709093
theorem B701651 : Blo 698317 701651 := bstep (se 1 (by rfl) ⟨526238, by rfl⟩ : syracuseStep 701651 = 1052477) B1052477
theorem B701667 : Blo 698317 701667 := bstep (se 1 (by rfl) ⟨526250, by rfl⟩ : syracuseStep 701667 = 1052501) B1052501
theorem B3552497 : Blo 698317 3552497 := bstep (se 2 (by rfl) ⟨1332186, by rfl⟩ : syracuseStep 3552497 = 2664373) B2664373
theorem B701683 : Blo 698317 701683 := bstep (se 1 (by rfl) ⟨526262, by rfl⟩ : syracuseStep 701683 = 1052525) B1052525
theorem B701699 : Blo 698317 701699 := bstep (se 1 (by rfl) ⟨526274, by rfl⟩ : syracuseStep 701699 = 1052549) B1052549
theorem B701715 : Blo 698317 701715 := bstep (se 1 (by rfl) ⟨526286, by rfl⟩ : syracuseStep 701715 = 1052573) B1052573
theorem B701731 : Blo 698317 701731 := bstep (se 1 (by rfl) ⟨526298, by rfl⟩ : syracuseStep 701731 = 1052597) B1052597
theorem B701747 : Blo 698317 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B701763 : Blo 698317 701763 := bstep (se 1 (by rfl) ⟨526322, by rfl⟩ : syracuseStep 701763 = 1052645) B1052645
theorem B701779 : Blo 698317 701779 := bstep (se 1 (by rfl) ⟨526334, by rfl⟩ : syracuseStep 701779 = 1052669) B1052669
theorem B701795 : Blo 698317 701795 := bstep (se 1 (by rfl) ⟨526346, by rfl⟩ : syracuseStep 701795 = 1052693) B1052693
theorem B701811 : Blo 698317 701811 := bstep (se 1 (by rfl) ⟨526358, by rfl⟩ : syracuseStep 701811 = 1052717) B1052717
theorem B701827 : Blo 698317 701827 := bstep (se 1 (by rfl) ⟨526370, by rfl⟩ : syracuseStep 701827 = 1052741) B1052741
theorem B701843 : Blo 698317 701843 := bstep (se 1 (by rfl) ⟨526382, by rfl⟩ : syracuseStep 701843 = 1052765) B1052765
theorem B701859 : Blo 698317 701859 := bstep (se 1 (by rfl) ⟨526394, by rfl⟩ : syracuseStep 701859 = 1052789) B1052789
theorem B701875 : Blo 698317 701875 := bstep (se 1 (by rfl) ⟨526406, by rfl⟩ : syracuseStep 701875 = 1052813) B1052813
theorem B701891 : Blo 698317 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B38352325 : Blo 698317 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B701907 : Blo 698317 701907 := bstep (se 1 (by rfl) ⟨526430, by rfl⟩ : syracuseStep 701907 = 1052861) B1052861
theorem B701923 : Blo 698317 701923 := bstep (se 1 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 701923 = 1052885) B1052885
theorem B701939 : Blo 698317 701939 := bstep (se 1 (by rfl) ⟨526454, by rfl⟩ : syracuseStep 701939 = 1052909) B1052909
theorem B701955 : Blo 698317 701955 := bstep (se 1 (by rfl) ⟨526466, by rfl⟩ : syracuseStep 701955 = 1052933) B1052933
theorem B701971 : Blo 698317 701971 := bstep (se 1 (by rfl) ⟨526478, by rfl⟩ : syracuseStep 701971 = 1052957) B1052957
theorem B701987 : Blo 698317 701987 := bstep (se 1 (by rfl) ⟨526490, by rfl⟩ : syracuseStep 701987 = 1052981) B1052981
theorem B702003 : Blo 698317 702003 := bstep (se 1 (by rfl) ⟨526502, by rfl⟩ : syracuseStep 702003 = 1053005) B1053005
theorem B702019 : Blo 698317 702019 := bstep (se 1 (by rfl) ⟨526514, by rfl⟩ : syracuseStep 702019 = 1053029) B1053029
theorem B702035 : Blo 698317 702035 := bstep (se 1 (by rfl) ⟨526526, by rfl⟩ : syracuseStep 702035 = 1053053) B1053053
theorem B702051 : Blo 698317 702051 := bstep (se 1 (by rfl) ⟨526538, by rfl⟩ : syracuseStep 702051 = 1053077) B1053077
theorem B702067 : Blo 698317 702067 := bstep (se 1 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 702067 = 1053101) B1053101
theorem B702083 : Blo 698317 702083 := bstep (se 1 (by rfl) ⟨526562, by rfl⟩ : syracuseStep 702083 = 1053125) B1053125
theorem B702099 : Blo 698317 702099 := bstep (se 1 (by rfl) ⟨526574, by rfl⟩ : syracuseStep 702099 = 1053149) B1053149
theorem B702115 : Blo 698317 702115 := bstep (se 1 (by rfl) ⟨526586, by rfl⟩ : syracuseStep 702115 = 1053173) B1053173
theorem B702131 : Blo 698317 702131 := bstep (se 1 (by rfl) ⟨526598, by rfl⟩ : syracuseStep 702131 = 1053197) B1053197
theorem B702147 : Blo 698317 702147 := bstep (se 1 (by rfl) ⟨526610, by rfl⟩ : syracuseStep 702147 = 1053221) B1053221
theorem B702163 : Blo 698317 702163 := bstep (se 1 (by rfl) ⟨526622, by rfl⟩ : syracuseStep 702163 = 1053245) B1053245
theorem B702179 : Blo 698317 702179 := bstep (se 1 (by rfl) ⟨526634, by rfl⟩ : syracuseStep 702179 = 1053269) B1053269
theorem B702195 : Blo 698317 702195 := bstep (se 1 (by rfl) ⟨526646, by rfl⟩ : syracuseStep 702195 = 1053293) B1053293
theorem B702211 : Blo 698317 702211 := bstep (se 1 (by rfl) ⟨526658, by rfl⟩ : syracuseStep 702211 = 1053317) B1053317
theorem B7976717 : Blo 698317 7976717 := bstep (se 3 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 7976717 = 2991269) B2991269
theorem B702227 : Blo 698317 702227 := bstep (se 1 (by rfl) ⟨526670, by rfl⟩ : syracuseStep 702227 = 1053341) B1053341
theorem B3979043 : Blo 698317 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B702243 : Blo 698317 702243 := bstep (se 1 (by rfl) ⟨526682, by rfl⟩ : syracuseStep 702243 = 1053365) B1053365
theorem B702259 : Blo 698317 702259 := bstep (se 1 (by rfl) ⟨526694, by rfl⟩ : syracuseStep 702259 = 1053389) B1053389
theorem B702275 : Blo 698317 702275 := bstep (se 1 (by rfl) ⟨526706, by rfl⟩ : syracuseStep 702275 = 1053413) B1053413
theorem B702291 : Blo 698317 702291 := bstep (se 1 (by rfl) ⟨526718, by rfl⟩ : syracuseStep 702291 = 1053437) B1053437
theorem B1259363 : Blo 698317 1259363 := bstep (se 1 (by rfl) ⟨944522, by rfl⟩ : syracuseStep 1259363 = 1889045) B1889045
theorem B702307 : Blo 698317 702307 := bstep (se 1 (by rfl) ⟨526730, by rfl⟩ : syracuseStep 702307 = 1053461) B1053461
theorem B997267 : Blo 698317 997267 := bstep (se 1 (by rfl) ⟨747950, by rfl⟩ : syracuseStep 997267 = 1495901) B1495901
theorem B997363 : Blo 698317 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B8534069 : Blo 698317 8534069 := bstep (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) B800069
theorem B2242723 : Blo 698317 2242723 := bstep (se 1 (by rfl) ⟨1682042, by rfl⟩ : syracuseStep 2242723 = 3364085) B3364085
theorem B997859 : Blo 698317 997859 := bstep (se 1 (by rfl) ⟨748394, by rfl⟩ : syracuseStep 997859 = 1496789) B1496789
theorem B3553955 : Blo 698317 3553955 := bstep (se 1 (by rfl) ⟨2665466, by rfl⟩ : syracuseStep 3553955 = 5330933) B5330933
theorem B2079533 : Blo 698317 2079533 := bstep (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) B779825
theorem B2243555 : Blo 698317 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B3783665 : Blo 698317 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B998497 : Blo 698317 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B1064083 : Blo 698317 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B1326385 : Blo 698317 1326385 := bstep (se 2 (by rfl) ⟨497394, by rfl⟩ : syracuseStep 1326385 = 994789) B994789
theorem B2243953 : Blo 698317 2243953 := bstep (se 2 (by rfl) ⟨841482, by rfl⟩ : syracuseStep 2243953 = 1682965) B1682965
theorem B2244017 : Blo 698317 2244017 := bstep (se 2 (by rfl) ⟨841506, by rfl⟩ : syracuseStep 2244017 = 1683013) B1683013
theorem B998833 : Blo 698317 998833 := bstep (se 2 (by rfl) ⟨374562, by rfl⟩ : syracuseStep 998833 = 749125) B749125
theorem B3554765 : Blo 698317 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B1064497 : Blo 698317 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B1064545 : Blo 698317 1064545 := bstep (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) B798409
theorem B3980933 : Blo 698317 3980933 := bstep (se 4 (by rfl) ⟨373212, by rfl⟩ : syracuseStep 3980933 = 746425) B746425
theorem B999425 : Blo 698317 999425 := bstep (se 2 (by rfl) ⟨374784, by rfl⟩ : syracuseStep 999425 = 749569) B749569
theorem B1327441 : Blo 698317 1327441 := bstep (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) B995581
theorem B999955 : Blo 698317 999955 := bstep (se 1 (by rfl) ⟨749966, by rfl⟩ : syracuseStep 999955 = 1499933) B1499933
theorem B7979633 : Blo 698317 7979633 := bstep (se 2 (by rfl) ⟨2992362, by rfl⟩ : syracuseStep 7979633 = 5984725) B5984725
theorem B1327843 : Blo 698317 1327843 := bstep (se 1 (by rfl) ⟨995882, by rfl⟩ : syracuseStep 1327843 = 1991765) B1991765
theorem B4801265 : Blo 698317 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B1327889 : Blo 698317 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B1065811 : Blo 698317 1065811 := bstep (se 1 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 1065811 = 1598717) B1598717
theorem B1622897 : Blo 698317 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B2999267 : Blo 698317 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B1328177 : Blo 698317 1328177 := bstep (se 2 (by rfl) ⟨498066, by rfl⟩ : syracuseStep 1328177 = 996133) B996133
theorem B1066321 : Blo 698317 1066321 := bstep (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) B799741
theorem B1328899 : Blo 698317 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B1492867 : Blo 698317 1492867 := bstep (se 1 (by rfl) ⟨1119650, by rfl⟩ : syracuseStep 1492867 = 2239301) B2239301
theorem B1066979 : Blo 698317 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B8407153 : Blo 698317 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B1329347 : Blo 698317 1329347 := bstep (se 1 (by rfl) ⟨997010, by rfl⟩ : syracuseStep 1329347 = 1994021) B1994021
theorem B5327045 : Blo 698317 5327045 := bstep (se 4 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 5327045 = 998821) B998821
theorem B3361009 : Blo 698317 3361009 := bstep (se 2 (by rfl) ⟨1260378, by rfl⟩ : syracuseStep 3361009 = 2520757) B2520757
theorem B1493329 : Blo 698317 1493329 := bstep (se 2 (by rfl) ⟨559998, by rfl⟩ : syracuseStep 1493329 = 1119997) B1119997
theorem B1067489 : Blo 698317 1067489 := bstep (se 2 (by rfl) ⟨400308, by rfl⟩ : syracuseStep 1067489 = 800617) B800617
theorem B6736355 : Blo 698317 6736355 := bstep (se 1 (by rfl) ⟨5052266, by rfl⟩ : syracuseStep 6736355 = 10104533) B10104533
theorem B1329635 : Blo 698317 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B4868579 : Blo 698317 4868579 := bstep (se 1 (by rfl) ⟨3651434, by rfl⟩ : syracuseStep 4868579 = 7302869) B7302869
theorem B1067683 : Blo 698317 1067683 := bstep (se 1 (by rfl) ⟨800762, by rfl⟩ : syracuseStep 1067683 = 1601525) B1601525
theorem B2837197 : Blo 698317 2837197 := bstep (se 3 (by rfl) ⟨531974, by rfl⟩ : syracuseStep 2837197 = 1063949) B1063949
theorem B10112141 : Blo 698317 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B1494371 : Blo 698317 1494371 := bstep (se 1 (by rfl) ⟨1120778, by rfl⟩ : syracuseStep 1494371 = 2241557) B2241557
theorem B1330577 : Blo 698317 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B1887715 : Blo 698317 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B708067 : Blo 698317 708067 := bstep (se 1 (by rfl) ⟨531050, by rfl⟩ : syracuseStep 708067 = 1062101) B1062101
theorem B2248195 : Blo 698317 2248195 := bstep (se 1 (by rfl) ⟨1686146, by rfl⟩ : syracuseStep 2248195 = 3372293) B3372293
theorem B6377201 : Blo 698317 6377201 := bstep (se 2 (by rfl) ⟨2391450, by rfl⟩ : syracuseStep 6377201 = 4782901) B4782901
theorem B4476707 : Blo 698317 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B1494883 : Blo 698317 1494883 := bstep (se 1 (by rfl) ⟨1121162, by rfl⟩ : syracuseStep 1494883 = 2242325) B2242325
theorem B1331473 : Blo 698317 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B1888589 : Blo 698317 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B1331633 : Blo 698317 1331633 := bstep (se 2 (by rfl) ⟨499362, by rfl⟩ : syracuseStep 1331633 = 998725) B998725
theorem B1495601 : Blo 698317 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B5034595 : Blo 698317 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B5034737 : Blo 698317 5034737 := bstep (se 2 (by rfl) ⟨1888026, by rfl⟩ : syracuseStep 5034737 = 3776053) B3776053
theorem B1332035 : Blo 698317 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B5034851 : Blo 698317 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B1135745 : Blo 698317 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B1889453 : Blo 698317 1889453 := bstep (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) B708545
theorem B1496387 : Blo 698317 1496387 := bstep (se 1 (by rfl) ⟨1122290, by rfl⟩ : syracuseStep 1496387 = 2244581) B2244581
theorem B3986765 : Blo 698317 3986765 := bstep (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) B1495037
theorem B1332931 : Blo 698317 1332931 := bstep (se 1 (by rfl) ⟨999698, by rfl⟩ : syracuseStep 1332931 = 1999397) B1999397
theorem B5986061 : Blo 698317 5986061 := bstep (se 3 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 5986061 = 2244773) B2244773
theorem B1333091 : Blo 698317 1333091 := bstep (se 1 (by rfl) ⟨999818, by rfl⟩ : syracuseStep 1333091 = 1999637) B1999637
theorem B841699 : Blo 698317 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B1988621 : Blo 698317 1988621 := bstep (se 3 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 1988621 = 745733) B745733
theorem B841843 : Blo 698317 841843 := bstep (se 1 (by rfl) ⟨631382, by rfl⟩ : syracuseStep 841843 = 1262765) B1262765
theorem B1890449 : Blo 698317 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B1988803 : Blo 698317 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B1988849 : Blo 698317 1988849 := bstep (se 2 (by rfl) ⟨745818, by rfl⟩ : syracuseStep 1988849 = 1491637) B1491637
theorem B1497361 : Blo 698317 1497361 := bstep (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) B1123021
theorem B1497617 : Blo 698317 1497617 := bstep (se 2 (by rfl) ⟨561606, by rfl⟩ : syracuseStep 1497617 = 1123213) B1123213
theorem B1890947 : Blo 698317 1890947 := bstep (se 1 (by rfl) ⟨1418210, by rfl⟩ : syracuseStep 1890947 = 2836421) B2836421
theorem B7592717 : Blo 698317 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B2153453 : Blo 698317 2153453 := bstep (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) B807545
theorem B15162677 : Blo 698317 15162677 := bstep (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) B1421501
theorem B3988997 : Blo 698317 3988997 := bstep (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) B747937
theorem B1990307 : Blo 698317 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B6741701 : Blo 698317 6741701 := bstep (se 4 (by rfl) ⟨632034, by rfl⟩ : syracuseStep 6741701 = 1264069) B1264069
theorem B4480753 : Blo 698317 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B1498915 : Blo 698317 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B5332877 : Blo 698317 5332877 := bstep (se 3 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 5332877 = 1999829) B1999829
theorem B3366947 : Blo 698317 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B9592901 : Blo 698317 9592901 := bstep (se 4 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 9592901 = 1798669) B1798669
theorem B4251761 : Blo 698317 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B1499249 : Blo 698317 1499249 := bstep (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) B1124437
theorem B3989681 : Blo 698317 3989681 := bstep (se 2 (by rfl) ⟨1496130, by rfl⟩ : syracuseStep 3989681 = 2992261) B2992261
theorem B1597649 : Blo 698317 1597649 := bstep (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) B1198237
theorem B4251953 : Blo 698317 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B2220419 : Blo 698317 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B1991537 : Blo 698317 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B3367793 : Blo 698317 3367793 := bstep (se 2 (by rfl) ⟨1262922, by rfl⟩ : syracuseStep 3367793 = 2525845) B2525845
theorem B12116963 : Blo 698317 12116963 := bstep (se 1 (by rfl) ⟨9087722, by rfl⟩ : syracuseStep 12116963 = 18175445) B18175445
theorem B1893347 : Blo 698317 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B1795139 : Blo 698317 1795139 := bstep (se 1 (by rfl) ⟨1346354, by rfl⟩ : syracuseStep 1795139 = 2692709) B2692709
theorem B7169093 : Blo 698317 7169093 := bstep (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) B1344205
theorem B3368141 : Blo 698317 3368141 := bstep (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) B1263053
theorem B746707 : Blo 698317 746707 := bstep (se 1 (by rfl) ⟨560030, by rfl⟩ : syracuseStep 746707 = 1120061) B1120061
theorem B1598897 : Blo 698317 1598897 := bstep (se 2 (by rfl) ⟨599586, by rfl⟩ : syracuseStep 1598897 = 1199173) B1199173
theorem B1009217 : Blo 698317 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B3991139 : Blo 698317 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B911027 : Blo 698317 911027 := bstep (se 1 (by rfl) ⟨683270, by rfl⟩ : syracuseStep 911027 = 1366541) B1366541
theorem B1599427 : Blo 698317 1599427 := bstep (se 1 (by rfl) ⟨1199570, by rfl⟩ : syracuseStep 1599427 = 2399141) B2399141
theorem B747587 : Blo 698317 747587 := bstep (se 1 (by rfl) ⟨560690, by rfl⟩ : syracuseStep 747587 = 1121381) B1121381
theorem B747715 : Blo 698317 747715 := bstep (se 1 (by rfl) ⟨560786, by rfl⟩ : syracuseStep 747715 = 1121573) B1121573
theorem B1992995 : Blo 698317 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B944467 : Blo 698317 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B2124397 : Blo 698317 2124397 := bstep (se 3 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 2124397 = 796649) B796649
theorem B10775267 : Blo 698317 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B4778801 : Blo 698317 4778801 := bstep (se 2 (by rfl) ⟨1792050, by rfl⟩ : syracuseStep 4778801 = 3584101) B3584101
theorem B2124785 : Blo 698317 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B748531 : Blo 698317 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B1993805 : Blo 698317 1993805 := bstep (se 3 (by rfl) ⟨373838, by rfl⟩ : syracuseStep 1993805 = 747677) B747677
theorem B1993997 : Blo 698317 1993997 := bstep (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) B747749
theorem B912691 : Blo 698317 912691 := bstep (se 1 (by rfl) ⟨684518, by rfl⟩ : syracuseStep 912691 = 1369037) B1369037
theorem B946003 : Blo 698317 946003 := bstep (se 1 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 946003 = 1419005) B1419005
theorem B1077121 : Blo 698317 1077121 := bstep (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) B807841
theorem B1011619 : Blo 698317 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B19132469 : Blo 698317 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B1896547 : Blo 698317 1896547 := bstep (se 1 (by rfl) ⟨1422410, by rfl⟩ : syracuseStep 1896547 = 2844821) B2844821
theorem B11989133 : Blo 698317 11989133 := bstep (se 3 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 11989133 = 4495925) B4495925
theorem B2846897 : Blo 698317 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B1994989 : Blo 698317 1994989 := bstep (se 3 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 1994989 = 748121) B748121
theorem B5304689 : Blo 698317 5304689 := bstep (se 2 (by rfl) ⟨1989258, by rfl⟩ : syracuseStep 5304689 = 3978517) B3978517
theorem B6386245 : Blo 698317 6386245 := bstep (se 4 (by rfl) ⟨598710, by rfl⟩ : syracuseStep 6386245 = 1197421) B1197421
theorem B1012403 : Blo 698317 1012403 := bstep (se 1 (by rfl) ⟨759302, by rfl⟩ : syracuseStep 1012403 = 1518605) B1518605
theorem B7959221 : Blo 698317 7959221 := bstep (se 5 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 7959221 = 746177) B746177
theorem B3994373 : Blo 698317 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B1897283 : Blo 698317 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B6714211 : Blo 698317 6714211 := bstep (se 1 (by rfl) ⟨5035658, by rfl⟩ : syracuseStep 6714211 = 10071317) B10071317
theorem B1897411 : Blo 698317 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B8090723 : Blo 698317 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B3994829 : Blo 698317 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B2651555 : Blo 698317 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B3601955 : Blo 698317 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B947971 : Blo 698317 947971 := bstep (se 1 (by rfl) ⟨710978, by rfl⟩ : syracuseStep 947971 = 1421957) B1421957
theorem B1800035 : Blo 698317 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B1996721 : Blo 698317 1996721 := bstep (se 2 (by rfl) ⟨748770, by rfl⟩ : syracuseStep 1996721 = 1497541) B1497541
theorem B2357261 : Blo 698317 2357261 := bstep (se 3 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 2357261 = 883973) B883973
theorem B2652209 : Blo 698317 2652209 := bstep (se 2 (by rfl) ⟨994578, by rfl⟩ : syracuseStep 2652209 = 1989157) B1989157
theorem B3536945 : Blo 698317 3536945 := bstep (se 2 (by rfl) ⟨1326354, by rfl⟩ : syracuseStep 3536945 = 2652709) B2652709
theorem B2357315 : Blo 698317 2357315 := bstep (se 1 (by rfl) ⟨1767986, by rfl⟩ : syracuseStep 2357315 = 3535973) B3535973
theorem B1996913 : Blo 698317 1996913 := bstep (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) B1497685
theorem B1800323 : Blo 698317 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B1767683 : Blo 698317 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B2357585 : Blo 698317 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B2161037 : Blo 698317 2161037 := bstep (se 3 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 2161037 = 810389) B810389
theorem B1571345 : Blo 698317 1571345 := bstep (se 2 (by rfl) ⟨589254, by rfl⟩ : syracuseStep 1571345 = 1178509) B1178509
theorem B1571363 : Blo 698317 1571363 := bstep (se 1 (by rfl) ⟨1178522, by rfl⟩ : syracuseStep 1571363 = 2357045) B2357045
theorem B1571633 : Blo 698317 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B1178435 : Blo 698317 1178435 := bstep (se 1 (by rfl) ⟨883826, by rfl⟩ : syracuseStep 1178435 = 1767653) B1767653
theorem B1571651 : Blo 698317 1571651 := bstep (se 1 (by rfl) ⟨1178738, by rfl⟩ : syracuseStep 1571651 = 2357477) B2357477
theorem B2358125 : Blo 698317 2358125 := bstep (se 3 (by rfl) ⟨442148, by rfl⟩ : syracuseStep 2358125 = 884297) B884297
theorem B2358179 : Blo 698317 2358179 := bstep (se 1 (by rfl) ⟨1768634, by rfl⟩ : syracuseStep 2358179 = 3537269) B3537269
theorem B1047491 : Blo 698317 1047491 := bstep (se 1 (by rfl) ⟨785618, by rfl⟩ : syracuseStep 1047491 = 1571237) B1571237
theorem B1178563 : Blo 698317 1178563 := bstep (se 1 (by rfl) ⟨883922, by rfl⟩ : syracuseStep 1178563 = 1767845) B1767845
theorem B1047521 : Blo 698317 1047521 := bstep (se 2 (by rfl) ⟨392820, by rfl⟩ : syracuseStep 1047521 = 785641) B785641
theorem B1047539 : Blo 698317 1047539 := bstep (se 1 (by rfl) ⟨785654, by rfl⟩ : syracuseStep 1047539 = 1571309) B1571309
theorem B1047569 : Blo 698317 1047569 := bstep (se 2 (by rfl) ⟨392838, by rfl⟩ : syracuseStep 1047569 = 785677) B785677
theorem B1047587 : Blo 698317 1047587 := bstep (se 1 (by rfl) ⟨785690, by rfl⟩ : syracuseStep 1047587 = 1571381) B1571381
theorem B1047617 : Blo 698317 1047617 := bstep (se 2 (by rfl) ⟨392856, by rfl⟩ : syracuseStep 1047617 = 785713) B785713
theorem B1178705 : Blo 698317 1178705 := bstep (se 2 (by rfl) ⟨442014, by rfl⟩ : syracuseStep 1178705 = 884029) B884029
theorem B1571921 : Blo 698317 1571921 := bstep (se 2 (by rfl) ⟨589470, by rfl⟩ : syracuseStep 1571921 = 1178941) B1178941
theorem B1047635 : Blo 698317 1047635 := bstep (se 1 (by rfl) ⟨785726, by rfl⟩ : syracuseStep 1047635 = 1571453) B1571453
theorem B1997905 : Blo 698317 1997905 := bstep (se 2 (by rfl) ⟨749214, by rfl⟩ : syracuseStep 1997905 = 1498429) B1498429
theorem B883811 : Blo 698317 883811 := bstep (se 1 (by rfl) ⟨662858, by rfl⟩ : syracuseStep 883811 = 1325717) B1325717
theorem B1571939 : Blo 698317 1571939 := bstep (se 1 (by rfl) ⟨1178954, by rfl⟩ : syracuseStep 1571939 = 2357909) B2357909
theorem B8649827 : Blo 698317 8649827 := bstep (se 1 (by rfl) ⟨6487370, by rfl⟩ : syracuseStep 8649827 = 12974741) B12974741
theorem B1047665 : Blo 698317 1047665 := bstep (se 2 (by rfl) ⟨392874, by rfl⟩ : syracuseStep 1047665 = 785749) B785749
theorem B1047683 : Blo 698317 1047683 := bstep (se 1 (by rfl) ⟨785762, by rfl⟩ : syracuseStep 1047683 = 1571525) B1571525
theorem B1047713 : Blo 698317 1047713 := bstep (se 2 (by rfl) ⟨392892, by rfl⟩ : syracuseStep 1047713 = 785785) B785785
theorem B1768625 : Blo 698317 1768625 := bstep (se 2 (by rfl) ⟨663234, by rfl⟩ : syracuseStep 1768625 = 1326469) B1326469
theorem B2358449 : Blo 698317 2358449 := bstep (se 2 (by rfl) ⟨884418, by rfl⟩ : syracuseStep 2358449 = 1768837) B1768837
theorem B1047731 : Blo 698317 1047731 := bstep (se 1 (by rfl) ⟨785798, by rfl⟩ : syracuseStep 1047731 = 1571597) B1571597
theorem B1047761 : Blo 698317 1047761 := bstep (se 2 (by rfl) ⟨392910, by rfl⟩ : syracuseStep 1047761 = 785821) B785821
theorem B1178833 : Blo 698317 1178833 := bstep (se 2 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 1178833 = 884125) B884125
theorem B1047779 : Blo 698317 1047779 := bstep (se 1 (by rfl) ⟨785834, by rfl⟩ : syracuseStep 1047779 = 1571669) B1571669
theorem B1768675 : Blo 698317 1768675 := bstep (se 1 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 1768675 = 2653013) B2653013
theorem B1178867 : Blo 698317 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B1047809 : Blo 698317 1047809 := bstep (se 2 (by rfl) ⟨392928, by rfl⟩ : syracuseStep 1047809 = 785857) B785857
theorem B1047827 : Blo 698317 1047827 := bstep (se 1 (by rfl) ⟨785870, by rfl⟩ : syracuseStep 1047827 = 1571741) B1571741
theorem B2424109 : Blo 698317 2424109 := bstep (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) B909041
theorem B1047857 : Blo 698317 1047857 := bstep (se 2 (by rfl) ⟨392946, by rfl⟩ : syracuseStep 1047857 = 785893) B785893
theorem B785731 : Blo 698317 785731 := bstep (se 1 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 785731 = 1178597) B1178597
theorem B1047875 : Blo 698317 1047875 := bstep (se 1 (by rfl) ⟨785906, by rfl⟩ : syracuseStep 1047875 = 1571813) B1571813
theorem B9567557 : Blo 698317 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B1047905 : Blo 698317 1047905 := bstep (se 2 (by rfl) ⟨392964, by rfl⟩ : syracuseStep 1047905 = 785929) B785929
theorem B1998179 : Blo 698317 1998179 := bstep (se 1 (by rfl) ⟨1498634, by rfl⟩ : syracuseStep 1998179 = 2997269) B2997269
theorem B1572209 : Blo 698317 1572209 := bstep (se 2 (by rfl) ⟨589578, by rfl⟩ : syracuseStep 1572209 = 1179157) B1179157
theorem B1768817 : Blo 698317 1768817 := bstep (se 2 (by rfl) ⟨663306, by rfl⟩ : syracuseStep 1768817 = 1326613) B1326613
theorem B1047923 : Blo 698317 1047923 := bstep (se 1 (by rfl) ⟨785942, by rfl⟩ : syracuseStep 1047923 = 1571885) B1571885
theorem B1178995 : Blo 698317 1178995 := bstep (se 1 (by rfl) ⟨884246, by rfl⟩ : syracuseStep 1178995 = 1768493) B1768493
theorem B1572227 : Blo 698317 1572227 := bstep (se 1 (by rfl) ⟨1179170, by rfl⟩ : syracuseStep 1572227 = 2358341) B2358341
theorem B1047953 : Blo 698317 1047953 := bstep (se 2 (by rfl) ⟨392982, by rfl⟩ : syracuseStep 1047953 = 785965) B785965
theorem B1047971 : Blo 698317 1047971 := bstep (se 1 (by rfl) ⟨785978, by rfl⟩ : syracuseStep 1047971 = 1571957) B1571957
theorem B1048001 : Blo 698317 1048001 := bstep (se 2 (by rfl) ⟨393000, by rfl⟩ : syracuseStep 1048001 = 786001) B786001
theorem B785875 : Blo 698317 785875 := bstep (se 1 (by rfl) ⟨589406, by rfl⟩ : syracuseStep 785875 = 1178813) B1178813
theorem B1048019 : Blo 698317 1048019 := bstep (se 1 (by rfl) ⟨786014, by rfl⟩ : syracuseStep 1048019 = 1572029) B1572029
theorem B2653667 : Blo 698317 2653667 := bstep (se 1 (by rfl) ⟨1990250, by rfl⟩ : syracuseStep 2653667 = 3980501) B3980501
theorem B3538403 : Blo 698317 3538403 := bstep (se 1 (by rfl) ⟨2653802, by rfl⟩ : syracuseStep 3538403 = 5307605) B5307605
theorem B1048049 : Blo 698317 1048049 := bstep (se 2 (by rfl) ⟨393018, by rfl⟩ : syracuseStep 1048049 = 786037) B786037
theorem B2653681 : Blo 698317 2653681 := bstep (se 2 (by rfl) ⟨995130, by rfl⟩ : syracuseStep 2653681 = 1990261) B1990261
theorem B1179137 : Blo 698317 1179137 := bstep (se 2 (by rfl) ⟨442176, by rfl⟩ : syracuseStep 1179137 = 884353) B884353
theorem B1048067 : Blo 698317 1048067 := bstep (se 1 (by rfl) ⟨786050, by rfl⟩ : syracuseStep 1048067 = 1572101) B1572101
theorem B1048097 : Blo 698317 1048097 := bstep (se 2 (by rfl) ⟨393036, by rfl⟩ : syracuseStep 1048097 = 786073) B786073
theorem B1998371 : Blo 698317 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B1048115 : Blo 698317 1048115 := bstep (se 1 (by rfl) ⟨786086, by rfl⟩ : syracuseStep 1048115 = 1572173) B1572173
theorem B1048145 : Blo 698317 1048145 := bstep (se 2 (by rfl) ⟨393054, by rfl⟩ : syracuseStep 1048145 = 786109) B786109
theorem B786019 : Blo 698317 786019 := bstep (se 1 (by rfl) ⟨589514, by rfl⟩ : syracuseStep 786019 = 1179029) B1179029
theorem B1048163 : Blo 698317 1048163 := bstep (se 1 (by rfl) ⟨786122, by rfl⟩ : syracuseStep 1048163 = 1572245) B1572245
theorem B4488803 : Blo 698317 4488803 := bstep (se 1 (by rfl) ⟨3366602, by rfl⟩ : syracuseStep 4488803 = 6733205) B6733205
theorem B1048193 : Blo 698317 1048193 := bstep (se 2 (by rfl) ⟨393072, by rfl⟩ : syracuseStep 1048193 = 786145) B786145
theorem B1179265 : Blo 698317 1179265 := bstep (se 2 (by rfl) ⟨442224, by rfl⟩ : syracuseStep 1179265 = 884449) B884449
theorem B1572497 : Blo 698317 1572497 := bstep (se 2 (by rfl) ⟨589686, by rfl⟩ : syracuseStep 1572497 = 1179373) B1179373
theorem B2391697 : Blo 698317 2391697 := bstep (se 2 (by rfl) ⟨896886, by rfl⟩ : syracuseStep 2391697 = 1793773) B1793773
theorem B1048211 : Blo 698317 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B1179299 : Blo 698317 1179299 := bstep (se 1 (by rfl) ⟨884474, by rfl⟩ : syracuseStep 1179299 = 1768949) B1768949
theorem B1572515 : Blo 698317 1572515 := bstep (se 1 (by rfl) ⟨1179386, by rfl⟩ : syracuseStep 1572515 = 2358773) B2358773
theorem B1048241 : Blo 698317 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B1048259 : Blo 698317 1048259 := bstep (se 1 (by rfl) ⟨786194, by rfl⟩ : syracuseStep 1048259 = 1572389) B1572389
theorem B2358989 : Blo 698317 2358989 := bstep (se 3 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 2358989 = 884621) B884621
theorem B1048289 : Blo 698317 1048289 := bstep (se 2 (by rfl) ⟨393108, by rfl⟩ : syracuseStep 1048289 = 786217) B786217
theorem B786163 : Blo 698317 786163 := bstep (se 1 (by rfl) ⟨589622, by rfl⟩ : syracuseStep 786163 = 1179245) B1179245
theorem B1048307 : Blo 698317 1048307 := bstep (se 1 (by rfl) ⟨786230, by rfl⟩ : syracuseStep 1048307 = 1572461) B1572461
theorem B2359043 : Blo 698317 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B1048337 : Blo 698317 1048337 := bstep (se 2 (by rfl) ⟨393126, by rfl⟩ : syracuseStep 1048337 = 786253) B786253
theorem B884515 : Blo 698317 884515 := bstep (se 1 (by rfl) ⟨663386, by rfl⟩ : syracuseStep 884515 = 1326773) B1326773
theorem B1048355 : Blo 698317 1048355 := bstep (se 1 (by rfl) ⟨786266, by rfl⟩ : syracuseStep 1048355 = 1572533) B1572533
theorem B1179427 : Blo 698317 1179427 := bstep (se 1 (by rfl) ⟨884570, by rfl⟩ : syracuseStep 1179427 = 1769141) B1769141
theorem B1048385 : Blo 698317 1048385 := bstep (se 2 (by rfl) ⟨393144, by rfl⟩ : syracuseStep 1048385 = 786289) B786289
theorem B1048403 : Blo 698317 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B1048433 : Blo 698317 1048433 := bstep (se 2 (by rfl) ⟨393162, by rfl⟩ : syracuseStep 1048433 = 786325) B786325
theorem B786307 : Blo 698317 786307 := bstep (se 1 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 786307 = 1179461) B1179461
theorem B884611 : Blo 698317 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B1048451 : Blo 698317 1048451 := bstep (se 1 (by rfl) ⟨786338, by rfl⟩ : syracuseStep 1048451 = 1572677) B1572677
theorem B1048481 : Blo 698317 1048481 := bstep (se 2 (by rfl) ⟨393180, by rfl⟩ : syracuseStep 1048481 = 786361) B786361
theorem B1179569 : Blo 698317 1179569 := bstep (se 2 (by rfl) ⟨442338, by rfl⟩ : syracuseStep 1179569 = 884677) B884677
theorem B1572785 : Blo 698317 1572785 := bstep (se 2 (by rfl) ⟨589794, by rfl⟩ : syracuseStep 1572785 = 1179589) B1179589
theorem B1048499 : Blo 698317 1048499 := bstep (se 1 (by rfl) ⟨786374, by rfl⟩ : syracuseStep 1048499 = 1572749) B1572749
theorem B1572803 : Blo 698317 1572803 := bstep (se 1 (by rfl) ⟨1179602, by rfl⟩ : syracuseStep 1572803 = 2359205) B2359205
theorem B1048529 : Blo 698317 1048529 := bstep (se 2 (by rfl) ⟨393198, by rfl⟩ : syracuseStep 1048529 = 786397) B786397
theorem B1048547 : Blo 698317 1048547 := bstep (se 1 (by rfl) ⟨786410, by rfl⟩ : syracuseStep 1048547 = 1572821) B1572821
theorem B1572875 : Blo 698317 1572875 := bstep (se 1 (by rfl) ⟨1179656, by rfl⟩ : syracuseStep 1572875 = 2359313) B2359313
theorem B1048601 : Blo 698317 1048601 := bstep (se 2 (by rfl) ⟨393225, by rfl⟩ : syracuseStep 1048601 = 786451) B786451
theorem B786487 : Blo 698317 786487 := bstep (se 1 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 786487 = 1179731) B1179731
theorem B1572929 : Blo 698317 1572929 := bstep (se 2 (by rfl) ⟨589848, by rfl⟩ : syracuseStep 1572929 = 1179697) B1179697
theorem B8978525 : Blo 698317 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B1048715 : Blo 698317 1048715 := bstep (se 1 (by rfl) ⟨786536, by rfl⟩ : syracuseStep 1048715 = 1573073) B1573073
theorem B1048727 : Blo 698317 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B2359475 : Blo 698317 2359475 := bstep (se 1 (by rfl) ⟨1769606, by rfl⟩ : syracuseStep 2359475 = 3539213) B3539213
theorem B1048793 : Blo 698317 1048793 := bstep (se 2 (by rfl) ⟨393297, by rfl⟩ : syracuseStep 1048793 = 786595) B786595
theorem B786667 : Blo 698317 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B1573145 : Blo 698317 1573145 := bstep (se 2 (by rfl) ⟨589929, by rfl⟩ : syracuseStep 1573145 = 1179859) B1179859
theorem B3997997 : Blo 698317 3997997 := bstep (se 3 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 3997997 = 1499249) B1499249
theorem B1048907 : Blo 698317 1048907 := bstep (se 1 (by rfl) ⟨786680, by rfl⟩ : syracuseStep 1048907 = 1573361) B1573361
theorem B1048919 : Blo 698317 1048919 := bstep (se 1 (by rfl) ⟨786689, by rfl⟩ : syracuseStep 1048919 = 1573379) B1573379
theorem B786775 : Blo 698317 786775 := bstep (se 1 (by rfl) ⟨590081, by rfl⟩ : syracuseStep 786775 = 1180163) B1180163
theorem B1573235 : Blo 698317 1573235 := bstep (se 1 (by rfl) ⟨1179926, by rfl⟩ : syracuseStep 1573235 = 2359853) B2359853
theorem B1573271 : Blo 698317 1573271 := bstep (se 1 (by rfl) ⟨1179953, by rfl⟩ : syracuseStep 1573271 = 2359907) B2359907
theorem B1180055 : Blo 698317 1180055 := bstep (se 1 (by rfl) ⟨885041, by rfl⟩ : syracuseStep 1180055 = 1770083) B1770083
theorem B1048985 : Blo 698317 1048985 := bstep (se 2 (by rfl) ⟨393369, by rfl⟩ : syracuseStep 1048985 = 786739) B786739
theorem B2359745 : Blo 698317 2359745 := bstep (se 2 (by rfl) ⟨884904, by rfl⟩ : syracuseStep 2359745 = 1769809) B1769809
theorem B1769921 : Blo 698317 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B1049099 : Blo 698317 1049099 := bstep (se 1 (by rfl) ⟨786824, by rfl⟩ : syracuseStep 1049099 = 1573649) B1573649
theorem B885259 : Blo 698317 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B786955 : Blo 698317 786955 := bstep (se 1 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 786955 = 1180433) B1180433
theorem B1180183 : Blo 698317 1180183 := bstep (se 1 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 1180183 = 1770275) B1770275
theorem B1049111 : Blo 698317 1049111 := bstep (se 1 (by rfl) ⟨786833, by rfl⟩ : syracuseStep 1049111 = 1573667) B1573667
theorem B4260397 : Blo 698317 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B1573451 : Blo 698317 1573451 := bstep (se 1 (by rfl) ⟨1180088, by rfl⟩ : syracuseStep 1573451 = 2360177) B2360177
theorem B1081931 : Blo 698317 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B1049177 : Blo 698317 1049177 := bstep (se 2 (by rfl) ⟨393441, by rfl⟩ : syracuseStep 1049177 = 786883) B786883
theorem B4489829 : Blo 698317 4489829 := bstep (se 4 (by rfl) ⟨420921, by rfl⟩ : syracuseStep 4489829 = 841843) B841843
theorem B787063 : Blo 698317 787063 := bstep (se 1 (by rfl) ⟨590297, by rfl⟩ : syracuseStep 787063 = 1180595) B1180595
theorem B1573505 : Blo 698317 1573505 := bstep (se 2 (by rfl) ⟨590064, by rfl⟩ : syracuseStep 1573505 = 1180129) B1180129
theorem B852619 : Blo 698317 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B1999511 : Blo 698317 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B1049291 : Blo 698317 1049291 := bstep (se 1 (by rfl) ⟨786968, by rfl⟩ : syracuseStep 1049291 = 1573937) B1573937
theorem B1049303 : Blo 698317 1049303 := bstep (se 1 (by rfl) ⟨786977, by rfl⟩ : syracuseStep 1049303 = 1573955) B1573955
theorem B1049369 : Blo 698317 1049369 := bstep (se 2 (by rfl) ⟨393513, by rfl⟩ : syracuseStep 1049369 = 787027) B787027
theorem B787243 : Blo 698317 787243 := bstep (se 1 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 787243 = 1180865) B1180865
theorem B852823 : Blo 698317 852823 := bstep (se 1 (by rfl) ⟨639617, by rfl⟩ : syracuseStep 852823 = 1279235) B1279235
theorem B1573721 : Blo 698317 1573721 := bstep (se 2 (by rfl) ⟨590145, by rfl⟩ : syracuseStep 1573721 = 1180291) B1180291
theorem B1049483 : Blo 698317 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B1049495 : Blo 698317 1049495 := bstep (se 1 (by rfl) ⟨787121, by rfl⟩ : syracuseStep 1049495 = 1574243) B1574243
theorem B787351 : Blo 698317 787351 := bstep (se 1 (by rfl) ⟨590513, by rfl⟩ : syracuseStep 787351 = 1181027) B1181027
theorem B1573811 : Blo 698317 1573811 := bstep (se 1 (by rfl) ⟨1180358, by rfl⟩ : syracuseStep 1573811 = 2360717) B2360717
theorem B1573847 : Blo 698317 1573847 := bstep (se 1 (by rfl) ⟨1180385, by rfl⟩ : syracuseStep 1573847 = 2360771) B2360771
theorem B1770457 : Blo 698317 1770457 := bstep (se 2 (by rfl) ⟨663921, by rfl⟩ : syracuseStep 1770457 = 1327843) B1327843
theorem B1049561 : Blo 698317 1049561 := bstep (se 2 (by rfl) ⟨393585, by rfl⟩ : syracuseStep 1049561 = 787171) B787171
theorem B2360285 : Blo 698317 2360285 := bstep (se 3 (by rfl) ⟨442553, by rfl⟩ : syracuseStep 2360285 = 885107) B885107
theorem B1049675 : Blo 698317 1049675 := bstep (se 1 (by rfl) ⟨787256, by rfl⟩ : syracuseStep 1049675 = 1574513) B1574513
theorem B787531 : Blo 698317 787531 := bstep (se 1 (by rfl) ⟨590648, by rfl⟩ : syracuseStep 787531 = 1181297) B1181297
theorem B1049687 : Blo 698317 1049687 := bstep (se 1 (by rfl) ⟨787265, by rfl⟩ : syracuseStep 1049687 = 1574531) B1574531
theorem B1574027 : Blo 698317 1574027 := bstep (se 1 (by rfl) ⟨1180520, by rfl⟩ : syracuseStep 1574027 = 2361041) B2361041
theorem B1180811 : Blo 698317 1180811 := bstep (se 1 (by rfl) ⟨885608, by rfl⟩ : syracuseStep 1180811 = 1771217) B1771217
theorem B1049753 : Blo 698317 1049753 := bstep (se 2 (by rfl) ⟨393657, by rfl⟩ : syracuseStep 1049753 = 787315) B787315
theorem B787639 : Blo 698317 787639 := bstep (se 1 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 787639 = 1181459) B1181459
theorem B1574081 : Blo 698317 1574081 := bstep (se 2 (by rfl) ⟨590280, by rfl⟩ : syracuseStep 1574081 = 1180561) B1180561
theorem B3540185 : Blo 698317 3540185 := bstep (se 2 (by rfl) ⟨1327569, by rfl⟩ : syracuseStep 3540185 = 2655139) B2655139
theorem B1180939 : Blo 698317 1180939 := bstep (se 1 (by rfl) ⟨885704, by rfl⟩ : syracuseStep 1180939 = 1771409) B1771409
theorem B1049867 : Blo 698317 1049867 := bstep (se 1 (by rfl) ⟨787400, by rfl⟩ : syracuseStep 1049867 = 1574801) B1574801
theorem B1049879 : Blo 698317 1049879 := bstep (se 1 (by rfl) ⟨787409, by rfl⟩ : syracuseStep 1049879 = 1574819) B1574819
theorem B1049945 : Blo 698317 1049945 := bstep (se 2 (by rfl) ⟨393729, by rfl⟩ : syracuseStep 1049945 = 787459) B787459
theorem B787819 : Blo 698317 787819 := bstep (se 1 (by rfl) ⟨590864, by rfl⟩ : syracuseStep 787819 = 1181729) B1181729
theorem B1574297 : Blo 698317 1574297 := bstep (se 2 (by rfl) ⟨590361, by rfl⟩ : syracuseStep 1574297 = 1180723) B1180723
theorem B1181081 : Blo 698317 1181081 := bstep (se 2 (by rfl) ⟨442905, by rfl⟩ : syracuseStep 1181081 = 885811) B885811
theorem B1050059 : Blo 698317 1050059 := bstep (se 1 (by rfl) ⟨787544, by rfl⟩ : syracuseStep 1050059 = 1575089) B1575089
theorem B5768653 : Blo 698317 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B1050071 : Blo 698317 1050071 := bstep (se 1 (by rfl) ⟨787553, by rfl⟩ : syracuseStep 1050071 = 1575107) B1575107
theorem B886231 : Blo 698317 886231 := bstep (se 1 (by rfl) ⟨664673, by rfl⟩ : syracuseStep 886231 = 1329347) B1329347
theorem B787927 : Blo 698317 787927 := bstep (se 1 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 787927 = 1181891) B1181891
theorem B1574387 : Blo 698317 1574387 := bstep (se 1 (by rfl) ⟨1180790, by rfl⟩ : syracuseStep 1574387 = 2361581) B2361581
theorem B1574423 : Blo 698317 1574423 := bstep (se 1 (by rfl) ⟨1180817, by rfl⟩ : syracuseStep 1574423 = 2361635) B2361635
theorem B1181209 : Blo 698317 1181209 := bstep (se 2 (by rfl) ⟨442953, by rfl⟩ : syracuseStep 1181209 = 885907) B885907
theorem B1050137 : Blo 698317 1050137 := bstep (se 2 (by rfl) ⟨393801, by rfl⟩ : syracuseStep 1050137 = 787603) B787603
theorem B2983513 : Blo 698317 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B1050251 : Blo 698317 1050251 := bstep (se 1 (by rfl) ⟨787688, by rfl⟩ : syracuseStep 1050251 = 1575377) B1575377
theorem B788107 : Blo 698317 788107 := bstep (se 1 (by rfl) ⟨591080, by rfl⟩ : syracuseStep 788107 = 1182161) B1182161
theorem B4490903 : Blo 698317 4490903 := bstep (se 1 (by rfl) ⟨3368177, by rfl⟩ : syracuseStep 4490903 = 6736355) B6736355
theorem B1050263 : Blo 698317 1050263 := bstep (se 1 (by rfl) ⟨787697, by rfl⟩ : syracuseStep 1050263 = 1575395) B1575395
theorem B3245719 : Blo 698317 3245719 := bstep (se 1 (by rfl) ⟨2434289, by rfl⟩ : syracuseStep 3245719 = 4868579) B4868579
theorem B1574603 : Blo 698317 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B1050329 : Blo 698317 1050329 := bstep (se 2 (by rfl) ⟨393873, by rfl⟩ : syracuseStep 1050329 = 787747) B787747
theorem B788215 : Blo 698317 788215 := bstep (se 1 (by rfl) ⟨591161, by rfl⟩ : syracuseStep 788215 = 1182323) B1182323
theorem B1574657 : Blo 698317 1574657 := bstep (se 2 (by rfl) ⟨590496, by rfl⟩ : syracuseStep 1574657 = 1180993) B1180993
theorem B1050443 : Blo 698317 1050443 := bstep (se 1 (by rfl) ⟨787832, by rfl⟩ : syracuseStep 1050443 = 1575665) B1575665
theorem B1050455 : Blo 698317 1050455 := bstep (se 1 (by rfl) ⟨787841, by rfl⟩ : syracuseStep 1050455 = 1575683) B1575683
theorem B1050521 : Blo 698317 1050521 := bstep (se 2 (by rfl) ⟨393945, by rfl⟩ : syracuseStep 1050521 = 787891) B787891
theorem B788395 : Blo 698317 788395 := bstep (se 1 (by rfl) ⟨591296, by rfl⟩ : syracuseStep 788395 = 1182593) B1182593
theorem B1574873 : Blo 698317 1574873 := bstep (se 2 (by rfl) ⟨590577, by rfl⟩ : syracuseStep 1574873 = 1181155) B1181155
theorem B1050635 : Blo 698317 1050635 := bstep (se 1 (by rfl) ⟨787976, by rfl⟩ : syracuseStep 1050635 = 1575953) B1575953
theorem B1050647 : Blo 698317 1050647 := bstep (se 1 (by rfl) ⟨787985, by rfl⟩ : syracuseStep 1050647 = 1575971) B1575971
theorem B788503 : Blo 698317 788503 := bstep (se 1 (by rfl) ⟨591377, by rfl⟩ : syracuseStep 788503 = 1182755) B1182755
theorem B1771571 : Blo 698317 1771571 := bstep (se 1 (by rfl) ⟨1328678, by rfl⟩ : syracuseStep 1771571 = 2657357) B2657357
theorem B1574963 : Blo 698317 1574963 := bstep (se 1 (by rfl) ⟨1181222, by rfl⟩ : syracuseStep 1574963 = 2362445) B2362445
theorem B2361419 : Blo 698317 2361419 := bstep (se 1 (by rfl) ⟨1771064, by rfl⟩ : syracuseStep 2361419 = 3542129) B3542129
theorem B1574999 : Blo 698317 1574999 := bstep (se 1 (by rfl) ⟨1181249, by rfl⟩ : syracuseStep 1574999 = 2362499) B2362499
theorem B1181783 : Blo 698317 1181783 := bstep (se 1 (by rfl) ⟨886337, by rfl⟩ : syracuseStep 1181783 = 1772675) B1772675
theorem B1050713 : Blo 698317 1050713 := bstep (se 2 (by rfl) ⟨394017, by rfl⟩ : syracuseStep 1050713 = 788035) B788035
theorem B1050827 : Blo 698317 1050827 := bstep (se 1 (by rfl) ⟨788120, by rfl⟩ : syracuseStep 1050827 = 1576241) B1576241
theorem B788683 : Blo 698317 788683 := bstep (se 1 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 788683 = 1183025) B1183025
theorem B1181911 : Blo 698317 1181911 := bstep (se 1 (by rfl) ⟨886433, by rfl⟩ : syracuseStep 1181911 = 1772867) B1772867
theorem B1050839 : Blo 698317 1050839 := bstep (se 1 (by rfl) ⟨788129, by rfl⟩ : syracuseStep 1050839 = 1576259) B1576259
theorem B1575179 : Blo 698317 1575179 := bstep (se 1 (by rfl) ⟨1181384, by rfl⟩ : syracuseStep 1575179 = 2362769) B2362769
theorem B887051 : Blo 698317 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B2885905 : Blo 698317 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B1050905 : Blo 698317 1050905 := bstep (se 2 (by rfl) ⟨394089, by rfl⟩ : syracuseStep 1050905 = 788179) B788179
theorem B27298093 : Blo 698317 27298093 := bstep (se 3 (by rfl) ⟨5118392, by rfl⟩ : syracuseStep 27298093 = 10236785) B10236785
theorem B788791 : Blo 698317 788791 := bstep (se 1 (by rfl) ⟨591593, by rfl⟩ : syracuseStep 788791 = 1183187) B1183187
theorem B1575233 : Blo 698317 1575233 := bstep (se 2 (by rfl) ⟨590712, by rfl⟩ : syracuseStep 1575233 = 1181425) B1181425
theorem B2361689 : Blo 698317 2361689 := bstep (se 2 (by rfl) ⟨885633, by rfl⟩ : syracuseStep 2361689 = 1771267) B1771267
theorem B1771865 : Blo 698317 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B1051019 : Blo 698317 1051019 := bstep (se 1 (by rfl) ⟨788264, by rfl⟩ : syracuseStep 1051019 = 1576529) B1576529
theorem B1051031 : Blo 698317 1051031 := bstep (se 1 (by rfl) ⟨788273, by rfl⟩ : syracuseStep 1051031 = 1576547) B1576547
theorem B1051097 : Blo 698317 1051097 := bstep (se 2 (by rfl) ⟨394161, by rfl⟩ : syracuseStep 1051097 = 788323) B788323
theorem B788971 : Blo 698317 788971 := bstep (se 1 (by rfl) ⟨591728, by rfl⟩ : syracuseStep 788971 = 1183457) B1183457
theorem B2984471 : Blo 698317 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B1575449 : Blo 698317 1575449 := bstep (se 2 (by rfl) ⟨590793, by rfl⟩ : syracuseStep 1575449 = 1181587) B1181587
theorem B1051211 : Blo 698317 1051211 := bstep (se 1 (by rfl) ⟨788408, by rfl⟩ : syracuseStep 1051211 = 1576817) B1576817
theorem B1051223 : Blo 698317 1051223 := bstep (se 1 (by rfl) ⟨788417, by rfl⟩ : syracuseStep 1051223 = 1576835) B1576835
theorem B789079 : Blo 698317 789079 := bstep (se 1 (by rfl) ⟨591809, by rfl⟩ : syracuseStep 789079 = 1183619) B1183619
theorem B2132569 : Blo 698317 2132569 := bstep (se 2 (by rfl) ⟨799713, by rfl⟩ : syracuseStep 2132569 = 1599427) B1599427
theorem B1575539 : Blo 698317 1575539 := bstep (se 1 (by rfl) ⟨1181654, by rfl⟩ : syracuseStep 1575539 = 2363309) B2363309
theorem B1575575 : Blo 698317 1575575 := bstep (se 1 (by rfl) ⟨1181681, by rfl⟩ : syracuseStep 1575575 = 2363363) B2363363
theorem B1051289 : Blo 698317 1051289 := bstep (se 2 (by rfl) ⟨394233, by rfl⟩ : syracuseStep 1051289 = 788467) B788467
theorem B1051403 : Blo 698317 1051403 := bstep (se 1 (by rfl) ⟨788552, by rfl⟩ : syracuseStep 1051403 = 1577105) B1577105
theorem B789259 : Blo 698317 789259 := bstep (se 1 (by rfl) ⟨591944, by rfl⟩ : syracuseStep 789259 = 1183889) B1183889
theorem B1051415 : Blo 698317 1051415 := bstep (se 1 (by rfl) ⟨788561, by rfl⟩ : syracuseStep 1051415 = 1577123) B1577123
theorem B3541805 : Blo 698317 3541805 := bstep (se 3 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 3541805 = 1328177) B1328177
theorem B2657069 : Blo 698317 2657069 := bstep (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) B996401
theorem B11209537 : Blo 698317 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B40897345 : Blo 698317 40897345 := bstep (se 2 (by rfl) ⟨15336504, by rfl⟩ : syracuseStep 40897345 = 30673009) B30673009
theorem B1575755 : Blo 698317 1575755 := bstep (se 1 (by rfl) ⟨1181816, by rfl⟩ : syracuseStep 1575755 = 2363633) B2363633
theorem B1182539 : Blo 698317 1182539 := bstep (se 1 (by rfl) ⟨886904, by rfl⟩ : syracuseStep 1182539 = 1773809) B1773809
theorem B1051481 : Blo 698317 1051481 := bstep (se 2 (by rfl) ⟨394305, by rfl⟩ : syracuseStep 1051481 = 788611) B788611
theorem B789367 : Blo 698317 789367 := bstep (se 1 (by rfl) ⟨592025, by rfl⟩ : syracuseStep 789367 = 1184051) B1184051
theorem B1575809 : Blo 698317 1575809 := bstep (se 2 (by rfl) ⟨590928, by rfl⟩ : syracuseStep 1575809 = 1181857) B1181857
theorem B887755 : Blo 698317 887755 := bstep (se 1 (by rfl) ⟨665816, by rfl⟩ : syracuseStep 887755 = 1331633) B1331633
theorem B1182667 : Blo 698317 1182667 := bstep (se 1 (by rfl) ⟨887000, by rfl⟩ : syracuseStep 1182667 = 1774001) B1774001
theorem B1051595 : Blo 698317 1051595 := bstep (se 1 (by rfl) ⟨788696, by rfl⟩ : syracuseStep 1051595 = 1577393) B1577393
theorem B1051607 : Blo 698317 1051607 := bstep (se 1 (by rfl) ⟨788705, by rfl⟩ : syracuseStep 1051607 = 1577411) B1577411
theorem B5311493 : Blo 698317 5311493 := bstep (se 4 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 5311493 = 995905) B995905
theorem B2362391 : Blo 698317 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B1051673 : Blo 698317 1051673 := bstep (se 2 (by rfl) ⟨394377, by rfl⟩ : syracuseStep 1051673 = 788755) B788755
theorem B789547 : Blo 698317 789547 := bstep (se 1 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 789547 = 1184321) B1184321
theorem B1576025 : Blo 698317 1576025 := bstep (se 2 (by rfl) ⟨591009, by rfl⟩ : syracuseStep 1576025 = 1182019) B1182019
theorem B1182809 : Blo 698317 1182809 := bstep (se 2 (by rfl) ⟨443553, by rfl⟩ : syracuseStep 1182809 = 887107) B887107
theorem B1051787 : Blo 698317 1051787 := bstep (se 1 (by rfl) ⟨788840, by rfl⟩ : syracuseStep 1051787 = 1577681) B1577681
theorem B1051799 : Blo 698317 1051799 := bstep (se 1 (by rfl) ⟨788849, by rfl⟩ : syracuseStep 1051799 = 1577699) B1577699
theorem B789655 : Blo 698317 789655 := bstep (se 1 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 789655 = 1184483) B1184483
theorem B1576115 : Blo 698317 1576115 := bstep (se 1 (by rfl) ⟨1182086, by rfl⟩ : syracuseStep 1576115 = 2364173) B2364173
theorem B1576151 : Blo 698317 1576151 := bstep (se 1 (by rfl) ⟨1182113, by rfl⟩ : syracuseStep 1576151 = 2364227) B2364227
theorem B888023 : Blo 698317 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B1182937 : Blo 698317 1182937 := bstep (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) B887203
theorem B1051865 : Blo 698317 1051865 := bstep (se 2 (by rfl) ⟨394449, by rfl⟩ : syracuseStep 1051865 = 788899) B788899
theorem B1051979 : Blo 698317 1051979 := bstep (se 1 (by rfl) ⟨788984, by rfl⟩ : syracuseStep 1051979 = 1577969) B1577969
theorem B789835 : Blo 698317 789835 := bstep (se 1 (by rfl) ⟨592376, by rfl⟩ : syracuseStep 789835 = 1184753) B1184753
theorem B1051991 : Blo 698317 1051991 := bstep (se 1 (by rfl) ⟨788993, by rfl⟩ : syracuseStep 1051991 = 1577987) B1577987
theorem B1576331 : Blo 698317 1576331 := bstep (se 1 (by rfl) ⟨1182248, by rfl⟩ : syracuseStep 1576331 = 2364497) B2364497
theorem B1052057 : Blo 698317 1052057 := bstep (se 2 (by rfl) ⟨394521, by rfl⟩ : syracuseStep 1052057 = 789043) B789043
theorem B789943 : Blo 698317 789943 := bstep (se 1 (by rfl) ⟨592457, by rfl⟩ : syracuseStep 789943 = 1184915) B1184915
theorem B1576385 : Blo 698317 1576385 := bstep (se 2 (by rfl) ⟨591144, by rfl⟩ : syracuseStep 1576385 = 1182289) B1182289
theorem B1052171 : Blo 698317 1052171 := bstep (se 1 (by rfl) ⟨789128, by rfl⟩ : syracuseStep 1052171 = 1578257) B1578257
theorem B1052183 : Blo 698317 1052183 := bstep (se 1 (by rfl) ⟨789137, by rfl⟩ : syracuseStep 1052183 = 1578275) B1578275
theorem B2657843 : Blo 698317 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B2362931 : Blo 698317 2362931 := bstep (se 1 (by rfl) ⟨1772198, by rfl⟩ : syracuseStep 2362931 = 3544397) B3544397
theorem B1052249 : Blo 698317 1052249 := bstep (se 2 (by rfl) ⟨394593, by rfl⟩ : syracuseStep 1052249 = 789187) B789187
theorem B1576601 : Blo 698317 1576601 := bstep (se 2 (by rfl) ⟨591225, by rfl⟩ : syracuseStep 1576601 = 1182451) B1182451
theorem B1052363 : Blo 698317 1052363 := bstep (se 1 (by rfl) ⟨789272, by rfl⟩ : syracuseStep 1052363 = 1578545) B1578545
theorem B1052375 : Blo 698317 1052375 := bstep (se 1 (by rfl) ⟨789281, by rfl⟩ : syracuseStep 1052375 = 1578563) B1578563
theorem B1576691 : Blo 698317 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B1576727 : Blo 698317 1576727 := bstep (se 1 (by rfl) ⟨1182545, by rfl⟩ : syracuseStep 1576727 = 2365091) B2365091
theorem B1183511 : Blo 698317 1183511 := bstep (se 1 (by rfl) ⟨887633, by rfl⟩ : syracuseStep 1183511 = 1775267) B1775267
theorem B1052441 : Blo 698317 1052441 := bstep (se 2 (by rfl) ⟨394665, by rfl⟩ : syracuseStep 1052441 = 789331) B789331
theorem B4263725 : Blo 698317 4263725 := bstep (se 3 (by rfl) ⟨799448, by rfl⟩ : syracuseStep 4263725 = 1598897) B1598897
theorem B2363201 : Blo 698317 2363201 := bstep (se 2 (by rfl) ⟨886200, by rfl⟩ : syracuseStep 2363201 = 1772401) B1772401
theorem B1052555 : Blo 698317 1052555 := bstep (se 1 (by rfl) ⟨789416, by rfl⟩ : syracuseStep 1052555 = 1578833) B1578833
theorem B1183639 : Blo 698317 1183639 := bstep (se 1 (by rfl) ⟨887729, by rfl⟩ : syracuseStep 1183639 = 1775459) B1775459
theorem B1052567 : Blo 698317 1052567 := bstep (se 1 (by rfl) ⟨789425, by rfl⟩ : syracuseStep 1052567 = 1578851) B1578851
theorem B888727 : Blo 698317 888727 := bstep (se 1 (by rfl) ⟨666545, by rfl⟩ : syracuseStep 888727 = 1333091) B1333091
theorem B1773515 : Blo 698317 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B1576907 : Blo 698317 1576907 := bstep (se 1 (by rfl) ⟨1182680, by rfl⟩ : syracuseStep 1576907 = 2365361) B2365361
theorem B5771213 : Blo 698317 5771213 := bstep (se 3 (by rfl) ⟨1082102, by rfl⟩ : syracuseStep 5771213 = 2164205) B2164205
theorem B1052633 : Blo 698317 1052633 := bstep (se 2 (by rfl) ⟨394737, by rfl⟩ : syracuseStep 1052633 = 789475) B789475
theorem B1576961 : Blo 698317 1576961 := bstep (se 2 (by rfl) ⟨591360, by rfl⟩ : syracuseStep 1576961 = 1182721) B1182721
theorem B1052747 : Blo 698317 1052747 := bstep (se 1 (by rfl) ⟨789560, by rfl⟩ : syracuseStep 1052747 = 1579121) B1579121
theorem B1052759 : Blo 698317 1052759 := bstep (se 1 (by rfl) ⟨789569, by rfl⟩ : syracuseStep 1052759 = 1579139) B1579139
theorem B9605213 : Blo 698317 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B1052825 : Blo 698317 1052825 := bstep (se 2 (by rfl) ⟨394809, by rfl⟩ : syracuseStep 1052825 = 789619) B789619
theorem B2691245 : Blo 698317 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B1577177 : Blo 698317 1577177 := bstep (se 2 (by rfl) ⟨591441, by rfl⟩ : syracuseStep 1577177 = 1182883) B1182883
theorem B1052939 : Blo 698317 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B1052951 : Blo 698317 1052951 := bstep (se 1 (by rfl) ⟨789713, by rfl⟩ : syracuseStep 1052951 = 1579427) B1579427
theorem B7180589 : Blo 698317 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B1577267 : Blo 698317 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B1577303 : Blo 698317 1577303 := bstep (se 1 (by rfl) ⟨1182977, by rfl⟩ : syracuseStep 1577303 = 2365955) B2365955
theorem B1053017 : Blo 698317 1053017 := bstep (se 2 (by rfl) ⟨394881, by rfl⟩ : syracuseStep 1053017 = 789763) B789763
theorem B2363741 : Blo 698317 2363741 := bstep (se 3 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 2363741 = 886403) B886403
theorem B1216921 : Blo 698317 1216921 := bstep (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) B912691
theorem B1053131 : Blo 698317 1053131 := bstep (se 1 (by rfl) ⟨789848, by rfl⟩ : syracuseStep 1053131 = 1579697) B1579697
theorem B1053143 : Blo 698317 1053143 := bstep (se 1 (by rfl) ⟨789857, by rfl⟩ : syracuseStep 1053143 = 1579715) B1579715
theorem B2429405 : Blo 698317 2429405 := bstep (se 3 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 2429405 = 911027) B911027
theorem B1577483 : Blo 698317 1577483 := bstep (se 1 (by rfl) ⟨1183112, by rfl⟩ : syracuseStep 1577483 = 2366225) B2366225
theorem B1184267 : Blo 698317 1184267 := bstep (se 1 (by rfl) ⟨888200, by rfl⟩ : syracuseStep 1184267 = 1776401) B1776401
theorem B1053209 : Blo 698317 1053209 := bstep (se 2 (by rfl) ⟨394953, by rfl⟩ : syracuseStep 1053209 = 789907) B789907
theorem B1577537 : Blo 698317 1577537 := bstep (se 2 (by rfl) ⟨591576, by rfl⟩ : syracuseStep 1577537 = 1183153) B1183153
theorem B1184395 : Blo 698317 1184395 := bstep (se 1 (by rfl) ⟨888296, by rfl⟩ : syracuseStep 1184395 = 1776593) B1776593
theorem B1053323 : Blo 698317 1053323 := bstep (se 1 (by rfl) ⟨789992, by rfl⟩ : syracuseStep 1053323 = 1579985) B1579985
theorem B1053335 : Blo 698317 1053335 := bstep (se 1 (by rfl) ⟨790001, by rfl⟩ : syracuseStep 1053335 = 1580003) B1580003
theorem B1053401 : Blo 698317 1053401 := bstep (se 2 (by rfl) ⟨395025, by rfl⟩ : syracuseStep 1053401 = 790051) B790051
theorem B2691863 : Blo 698317 2691863 := bstep (se 1 (by rfl) ⟨2018897, by rfl⟩ : syracuseStep 2691863 = 4037795) B4037795
theorem B1577753 : Blo 698317 1577753 := bstep (se 2 (by rfl) ⟨591657, by rfl⟩ : syracuseStep 1577753 = 1183315) B1183315
theorem B1184537 : Blo 698317 1184537 := bstep (se 2 (by rfl) ⟨444201, by rfl⟩ : syracuseStep 1184537 = 888403) B888403
theorem B1577843 : Blo 698317 1577843 := bstep (se 1 (by rfl) ⟨1183382, by rfl⟩ : syracuseStep 1577843 = 2366765) B2366765
theorem B1774487 : Blo 698317 1774487 := bstep (se 1 (by rfl) ⟨1330865, by rfl⟩ : syracuseStep 1774487 = 2661731) B2661731
theorem B1577879 : Blo 698317 1577879 := bstep (se 1 (by rfl) ⟨1183409, by rfl⟩ : syracuseStep 1577879 = 2366819) B2366819
theorem B1184665 : Blo 698317 1184665 := bstep (se 2 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 1184665 = 888499) B888499
theorem B2659331 : Blo 698317 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B1578059 : Blo 698317 1578059 := bstep (se 1 (by rfl) ⟨1183544, by rfl⟩ : syracuseStep 1578059 = 2367089) B2367089
theorem B2331737 : Blo 698317 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B1578113 : Blo 698317 1578113 := bstep (se 2 (by rfl) ⟨591792, by rfl⟩ : syracuseStep 1578113 = 1183585) B1183585
theorem B4494467 : Blo 698317 4494467 := bstep (se 1 (by rfl) ⟨3370850, by rfl⟩ : syracuseStep 4494467 = 6741701) B6741701
theorem B1348825 : Blo 698317 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B1578329 : Blo 698317 1578329 := bstep (se 2 (by rfl) ⟨591873, by rfl⟩ : syracuseStep 1578329 = 1183747) B1183747
theorem B5313923 : Blo 698317 5313923 := bstep (se 1 (by rfl) ⟨3985442, by rfl⟩ : syracuseStep 5313923 = 7970885) B7970885
theorem B6395267 : Blo 698317 6395267 := bstep (se 1 (by rfl) ⟨4796450, by rfl⟩ : syracuseStep 6395267 = 9592901) B9592901
theorem B1578419 : Blo 698317 1578419 := bstep (se 1 (by rfl) ⟨1183814, by rfl⟩ : syracuseStep 1578419 = 2367629) B2367629
theorem B2659787 : Blo 698317 2659787 := bstep (se 1 (by rfl) ⟨1994840, by rfl⟩ : syracuseStep 2659787 = 3989681) B3989681
theorem B2364875 : Blo 698317 2364875 := bstep (se 1 (by rfl) ⟨1773656, by rfl⟩ : syracuseStep 2364875 = 3547313) B3547313
theorem B1578455 : Blo 698317 1578455 := bstep (se 1 (by rfl) ⟨1183841, by rfl⟩ : syracuseStep 1578455 = 2367683) B2367683
theorem B2528729 : Blo 698317 2528729 := bstep (se 2 (by rfl) ⟨948273, by rfl⟩ : syracuseStep 2528729 = 1896547) B1896547
theorem B1775155 : Blo 698317 1775155 := bstep (se 1 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 1775155 = 2662733) B2662733
theorem B1480279 : Blo 698317 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B1578635 : Blo 698317 1578635 := bstep (se 1 (by rfl) ⟨1183976, by rfl⟩ : syracuseStep 1578635 = 2367953) B2367953
theorem B2659985 : Blo 698317 2659985 := bstep (se 2 (by rfl) ⟨997494, by rfl⟩ : syracuseStep 2659985 = 1994989) B1994989
theorem B1775297 : Blo 698317 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B1578689 : Blo 698317 1578689 := bstep (se 2 (by rfl) ⟨592008, by rfl⟩ : syracuseStep 1578689 = 1184017) B1184017
theorem B2365145 : Blo 698317 2365145 := bstep (se 2 (by rfl) ⟨886929, by rfl⟩ : syracuseStep 2365145 = 1773859) B1773859
theorem B2987921 : Blo 698317 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B1120151 : Blo 698317 1120151 := bstep (se 1 (by rfl) ⟨840113, by rfl⟩ : syracuseStep 1120151 = 1680227) B1680227
theorem B1578905 : Blo 698317 1578905 := bstep (se 2 (by rfl) ⟨592089, by rfl⟩ : syracuseStep 1578905 = 1184179) B1184179
theorem B1578995 : Blo 698317 1578995 := bstep (se 1 (by rfl) ⟨1184246, by rfl⟩ : syracuseStep 1578995 = 2368493) B2368493
theorem B1579031 : Blo 698317 1579031 := bstep (se 1 (by rfl) ⟨1184273, by rfl⟩ : syracuseStep 1579031 = 2368547) B2368547
theorem B2726081 : Blo 698317 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B1579211 : Blo 698317 1579211 := bstep (se 1 (by rfl) ⟨1184408, by rfl⟩ : syracuseStep 1579211 = 2368817) B2368817
theorem B1513687 : Blo 698317 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B1579265 : Blo 698317 1579265 := bstep (se 2 (by rfl) ⟨592224, by rfl⟩ : syracuseStep 1579265 = 1184449) B1184449
theorem B1120663 : Blo 698317 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B2660759 : Blo 698317 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B2365847 : Blo 698317 2365847 := bstep (se 1 (by rfl) ⟨1774385, by rfl⟩ : syracuseStep 2365847 = 3548771) B3548771
theorem B8952281 : Blo 698317 8952281 := bstep (se 2 (by rfl) ⟨3357105, by rfl⟩ : syracuseStep 8952281 = 6714211) B6714211
theorem B1579481 : Blo 698317 1579481 := bstep (se 2 (by rfl) ⟨592305, by rfl⟩ : syracuseStep 1579481 = 1184611) B1184611
theorem B34970129 : Blo 698317 34970129 := bstep (se 2 (by rfl) ⟨13113798, by rfl⟩ : syracuseStep 34970129 = 26227597) B26227597
theorem B1579571 : Blo 698317 1579571 := bstep (se 1 (by rfl) ⟨1184678, by rfl⟩ : syracuseStep 1579571 = 2369357) B2369357
theorem B1579607 : Blo 698317 1579607 := bstep (se 1 (by rfl) ⟨1184705, by rfl⟩ : syracuseStep 1579607 = 2369411) B2369411
theorem B2529881 : Blo 698317 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B3545693 : Blo 698317 3545693 := bstep (se 3 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 3545693 = 1329635) B1329635
theorem B2660957 : Blo 698317 2660957 := bstep (se 3 (by rfl) ⟨498929, by rfl⟩ : syracuseStep 2660957 = 997859) B997859
theorem B1645171 : Blo 698317 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B5380739 : Blo 698317 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B1121035 : Blo 698317 1121035 := bstep (se 1 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 1121035 = 1681553) B1681553
theorem B1579787 : Blo 698317 1579787 := bstep (se 1 (by rfl) ⟨1184840, by rfl⟩ : syracuseStep 1579787 = 2369681) B2369681
theorem B2988845 : Blo 698317 2988845 := bstep (se 3 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 2988845 = 1120817) B1120817
theorem B1579841 : Blo 698317 1579841 := bstep (se 2 (by rfl) ⟨592440, by rfl⟩ : syracuseStep 1579841 = 1184881) B1184881
theorem B2366387 : Blo 698317 2366387 := bstep (se 1 (by rfl) ⟨1774790, by rfl⟩ : syracuseStep 2366387 = 3549581) B3549581
theorem B1776563 : Blo 698317 1776563 := bstep (se 1 (by rfl) ⟨1332422, by rfl⟩ : syracuseStep 1776563 = 2664845) B2664845
theorem B1121291 : Blo 698317 1121291 := bstep (se 1 (by rfl) ⟨840968, by rfl⟩ : syracuseStep 1121291 = 1681937) B1681937
theorem B1580057 : Blo 698317 1580057 := bstep (se 2 (by rfl) ⟨592521, by rfl⟩ : syracuseStep 1580057 = 1185043) B1185043
theorem B1580147 : Blo 698317 1580147 := bstep (se 1 (by rfl) ⟨1185110, by rfl⟩ : syracuseStep 1580147 = 2370221) B2370221
theorem B7183511 : Blo 698317 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B1580183 : Blo 698317 1580183 := bstep (se 1 (by rfl) ⟨1185137, by rfl⟩ : syracuseStep 1580183 = 2370275) B2370275
theorem B2366657 : Blo 698317 2366657 := bstep (se 2 (by rfl) ⟨887496, by rfl⟩ : syracuseStep 2366657 = 1774993) B1774993
theorem B3185867 : Blo 698317 3185867 := bstep (se 1 (by rfl) ⟨2389400, by rfl⟩ : syracuseStep 3185867 = 4778801) B4778801
theorem B1121483 : Blo 698317 1121483 := bstep (se 1 (by rfl) ⟨841112, by rfl⟩ : syracuseStep 1121483 = 1682225) B1682225
theorem B2563379 : Blo 698317 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B1416523 : Blo 698317 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1777099 : Blo 698317 1777099 := bstep (se 1 (by rfl) ⟨1332824, by rfl⟩ : syracuseStep 1777099 = 2665649) B2665649
theorem B1777241 : Blo 698317 1777241 := bstep (se 2 (by rfl) ⟨666465, by rfl⟩ : syracuseStep 1777241 = 1332931) B1332931
theorem B2367197 : Blo 698317 2367197 := bstep (se 3 (by rfl) ⟨443849, by rfl⟩ : syracuseStep 2367197 = 887699) B887699
theorem B3776357 : Blo 698317 3776357 := bstep (se 4 (by rfl) ⟨354033, by rfl⟩ : syracuseStep 3776357 = 708067) B708067
theorem B2695091 : Blo 698317 2695091 := bstep (se 1 (by rfl) ⟨2021318, by rfl⟩ : syracuseStep 2695091 = 4042637) B4042637
theorem B5742541 : Blo 698317 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B1122265 : Blo 698317 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B12754979 : Blo 698317 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B2990297 : Blo 698317 2990297 := bstep (se 2 (by rfl) ⟨1121361, by rfl⟩ : syracuseStep 2990297 = 2242723) B2242723
theorem B3776813 : Blo 698317 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B2662915 : Blo 698317 2662915 := bstep (se 1 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 2662915 = 3994373) B3994373
theorem B5677573 : Blo 698317 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B3547799 : Blo 698317 3547799 := bstep (se 1 (by rfl) ⟨2660849, by rfl⟩ : syracuseStep 3547799 = 5321699) B5321699
theorem B5317325 : Blo 698317 5317325 := bstep (se 3 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 5317325 = 1993997) B1993997
theorem B2663219 : Blo 698317 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B2368331 : Blo 698317 2368331 := bstep (se 1 (by rfl) ⟨1776248, by rfl⟩ : syracuseStep 2368331 = 3552497) B3552497
theorem B2368601 : Blo 698317 2368601 := bstep (se 2 (by rfl) ⟨888225, by rfl⟩ : syracuseStep 2368601 = 1776451) B1776451
theorem B5317811 : Blo 698317 5317811 := bstep (se 1 (by rfl) ⟨3988358, by rfl⟩ : syracuseStep 5317811 = 7976717) B7976717
theorem B2663873 : Blo 698317 2663873 := bstep (se 2 (by rfl) ⟨998952, by rfl⟩ : syracuseStep 2663873 = 1997905) B1997905
theorem B1418777 : Blo 698317 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B2369303 : Blo 698317 2369303 := bstep (se 1 (by rfl) ⟨1776977, by rfl⟩ : syracuseStep 2369303 = 3553955) B3553955
theorem B2991937 : Blo 698317 2991937 := bstep (se 2 (by rfl) ⟨1121976, by rfl⟩ : syracuseStep 2991937 = 2243953) B2243953
theorem B1386355 : Blo 698317 1386355 := bstep (se 1 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 1386355 = 2079533) B2079533
theorem B698327 : Blo 698317 698327 := bstep (se 1 (by rfl) ⟨523745, by rfl⟩ : syracuseStep 698327 = 1047491) B1047491
theorem B698347 : Blo 698317 698347 := bstep (se 1 (by rfl) ⟨523760, by rfl⟩ : syracuseStep 698347 = 1047521) B1047521
theorem B698359 : Blo 698317 698359 := bstep (se 1 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 698359 = 1047539) B1047539
theorem B698379 : Blo 698317 698379 := bstep (se 1 (by rfl) ⟨523784, by rfl⟩ : syracuseStep 698379 = 1047569) B1047569
theorem B698391 : Blo 698317 698391 := bstep (se 1 (by rfl) ⟨523793, by rfl⟩ : syracuseStep 698391 = 1047587) B1047587
theorem B698411 : Blo 698317 698411 := bstep (se 1 (by rfl) ⟨523808, by rfl⟩ : syracuseStep 698411 = 1047617) B1047617
theorem B698423 : Blo 698317 698423 := bstep (se 1 (by rfl) ⟨523817, by rfl⟩ : syracuseStep 698423 = 1047635) B1047635
theorem B1419329 : Blo 698317 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B698443 : Blo 698317 698443 := bstep (se 1 (by rfl) ⟨523832, by rfl⟩ : syracuseStep 698443 = 1047665) B1047665
theorem B698455 : Blo 698317 698455 := bstep (se 1 (by rfl) ⟨523841, by rfl⟩ : syracuseStep 698455 = 1047683) B1047683
theorem B698475 : Blo 698317 698475 := bstep (se 1 (by rfl) ⟨523856, by rfl⟩ : syracuseStep 698475 = 1047713) B1047713
theorem B698487 : Blo 698317 698487 := bstep (se 1 (by rfl) ⟨523865, by rfl⟩ : syracuseStep 698487 = 1047731) B1047731
theorem B698507 : Blo 698317 698507 := bstep (se 1 (by rfl) ⟨523880, by rfl⟩ : syracuseStep 698507 = 1047761) B1047761
theorem B698519 : Blo 698317 698519 := bstep (se 1 (by rfl) ⟨523889, by rfl⟩ : syracuseStep 698519 = 1047779) B1047779
theorem B698539 : Blo 698317 698539 := bstep (se 1 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 698539 = 1047809) B1047809
theorem B698551 : Blo 698317 698551 := bstep (se 1 (by rfl) ⟨523913, by rfl⟩ : syracuseStep 698551 = 1047827) B1047827
theorem B3188929 : Blo 698317 3188929 := bstep (se 2 (by rfl) ⟨1195848, by rfl⟩ : syracuseStep 3188929 = 2391697) B2391697
theorem B698571 : Blo 698317 698571 := bstep (se 1 (by rfl) ⟨523928, by rfl⟩ : syracuseStep 698571 = 1047857) B1047857
theorem B698583 : Blo 698317 698583 := bstep (se 1 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 698583 = 1047875) B1047875
theorem B698603 : Blo 698317 698603 := bstep (se 1 (by rfl) ⟨523952, by rfl⟩ : syracuseStep 698603 = 1047905) B1047905
theorem B698615 : Blo 698317 698615 := bstep (se 1 (by rfl) ⟨523961, by rfl⟩ : syracuseStep 698615 = 1047923) B1047923
theorem B698635 : Blo 698317 698635 := bstep (se 1 (by rfl) ⟨523976, by rfl⟩ : syracuseStep 698635 = 1047953) B1047953
theorem B698647 : Blo 698317 698647 := bstep (se 1 (by rfl) ⟨523985, by rfl⟩ : syracuseStep 698647 = 1047971) B1047971
theorem B698667 : Blo 698317 698667 := bstep (se 1 (by rfl) ⟨524000, by rfl⟩ : syracuseStep 698667 = 1048001) B1048001
theorem B2369843 : Blo 698317 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B698679 : Blo 698317 698679 := bstep (se 1 (by rfl) ⟨524009, by rfl⟩ : syracuseStep 698679 = 1048019) B1048019
theorem B5974337 : Blo 698317 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B698699 : Blo 698317 698699 := bstep (se 1 (by rfl) ⟨524024, by rfl⟩ : syracuseStep 698699 = 1048049) B1048049
theorem B698711 : Blo 698317 698711 := bstep (se 1 (by rfl) ⟨524033, by rfl⟩ : syracuseStep 698711 = 1048067) B1048067
theorem B698731 : Blo 698317 698731 := bstep (se 1 (by rfl) ⟨524048, by rfl⟩ : syracuseStep 698731 = 1048097) B1048097
theorem B698743 : Blo 698317 698743 := bstep (se 1 (by rfl) ⟨524057, by rfl⟩ : syracuseStep 698743 = 1048115) B1048115
theorem B698763 : Blo 698317 698763 := bstep (se 1 (by rfl) ⟨524072, by rfl⟩ : syracuseStep 698763 = 1048145) B1048145
theorem B698775 : Blo 698317 698775 := bstep (se 1 (by rfl) ⟨524081, by rfl⟩ : syracuseStep 698775 = 1048163) B1048163
theorem B2992535 : Blo 698317 2992535 := bstep (se 1 (by rfl) ⟨2244401, by rfl⟩ : syracuseStep 2992535 = 4488803) B4488803
theorem B698795 : Blo 698317 698795 := bstep (se 1 (by rfl) ⟨524096, by rfl⟩ : syracuseStep 698795 = 1048193) B1048193
theorem B698807 : Blo 698317 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B698827 : Blo 698317 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B698839 : Blo 698317 698839 := bstep (se 1 (by rfl) ⟨524129, by rfl⟩ : syracuseStep 698839 = 1048259) B1048259
theorem B698859 : Blo 698317 698859 := bstep (se 1 (by rfl) ⟨524144, by rfl⟩ : syracuseStep 698859 = 1048289) B1048289
theorem B698871 : Blo 698317 698871 := bstep (se 1 (by rfl) ⟨524153, by rfl⟩ : syracuseStep 698871 = 1048307) B1048307
theorem B698891 : Blo 698317 698891 := bstep (se 1 (by rfl) ⟨524168, by rfl⟩ : syracuseStep 698891 = 1048337) B1048337
theorem B698903 : Blo 698317 698903 := bstep (se 1 (by rfl) ⟨524177, by rfl⟩ : syracuseStep 698903 = 1048355) B1048355
theorem B698923 : Blo 698317 698923 := bstep (se 1 (by rfl) ⟨524192, by rfl⟩ : syracuseStep 698923 = 1048385) B1048385
theorem B698935 : Blo 698317 698935 := bstep (se 1 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 698935 = 1048403) B1048403
theorem B2370113 : Blo 698317 2370113 := bstep (se 2 (by rfl) ⟨888792, by rfl⟩ : syracuseStep 2370113 = 1777585) B1777585
theorem B698955 : Blo 698317 698955 := bstep (se 1 (by rfl) ⟨524216, by rfl⟩ : syracuseStep 698955 = 1048433) B1048433
theorem B698967 : Blo 698317 698967 := bstep (se 1 (by rfl) ⟨524225, by rfl⟩ : syracuseStep 698967 = 1048451) B1048451
theorem B5319269 : Blo 698317 5319269 := bstep (se 4 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 5319269 = 997363) B997363
theorem B698987 : Blo 698317 698987 := bstep (se 1 (by rfl) ⟨524240, by rfl⟩ : syracuseStep 698987 = 1048481) B1048481
theorem B698999 : Blo 698317 698999 := bstep (se 1 (by rfl) ⟨524249, by rfl⟩ : syracuseStep 698999 = 1048499) B1048499
theorem B699019 : Blo 698317 699019 := bstep (se 1 (by rfl) ⟨524264, by rfl⟩ : syracuseStep 699019 = 1048529) B1048529
theorem B699031 : Blo 698317 699031 := bstep (se 1 (by rfl) ⟨524273, by rfl⟩ : syracuseStep 699031 = 1048547) B1048547
theorem B699051 : Blo 698317 699051 := bstep (se 1 (by rfl) ⟨524288, by rfl⟩ : syracuseStep 699051 = 1048577) B1048577
theorem B2665133 : Blo 698317 2665133 := bstep (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) B999425
theorem B699063 : Blo 698317 699063 := bstep (se 1 (by rfl) ⟨524297, by rfl⟩ : syracuseStep 699063 = 1048595) B1048595
theorem B699083 : Blo 698317 699083 := bstep (se 1 (by rfl) ⟨524312, by rfl⟩ : syracuseStep 699083 = 1048625) B1048625
theorem B2665163 : Blo 698317 2665163 := bstep (se 1 (by rfl) ⟨1998872, by rfl⟩ : syracuseStep 2665163 = 3997745) B3997745
theorem B699095 : Blo 698317 699095 := bstep (se 1 (by rfl) ⟨524321, by rfl⟩ : syracuseStep 699095 = 1048643) B1048643
theorem B699115 : Blo 698317 699115 := bstep (se 1 (by rfl) ⟨524336, by rfl⟩ : syracuseStep 699115 = 1048673) B1048673
theorem B699127 : Blo 698317 699127 := bstep (se 1 (by rfl) ⟨524345, by rfl⟩ : syracuseStep 699127 = 1048691) B1048691
theorem B699147 : Blo 698317 699147 := bstep (se 1 (by rfl) ⟨524360, by rfl⟩ : syracuseStep 699147 = 1048721) B1048721
theorem B699159 : Blo 698317 699159 := bstep (se 1 (by rfl) ⟨524369, by rfl⟩ : syracuseStep 699159 = 1048739) B1048739
theorem B699179 : Blo 698317 699179 := bstep (se 1 (by rfl) ⟨524384, by rfl⟩ : syracuseStep 699179 = 1048769) B1048769
theorem B699191 : Blo 698317 699191 := bstep (se 1 (by rfl) ⟨524393, by rfl⟩ : syracuseStep 699191 = 1048787) B1048787
theorem B699211 : Blo 698317 699211 := bstep (se 1 (by rfl) ⟨524408, by rfl⟩ : syracuseStep 699211 = 1048817) B1048817
theorem B699223 : Blo 698317 699223 := bstep (se 1 (by rfl) ⟨524417, by rfl⟩ : syracuseStep 699223 = 1048835) B1048835
theorem B699243 : Blo 698317 699243 := bstep (se 1 (by rfl) ⟨524432, by rfl⟩ : syracuseStep 699243 = 1048865) B1048865
theorem B699255 : Blo 698317 699255 := bstep (se 1 (by rfl) ⟨524441, by rfl⟩ : syracuseStep 699255 = 1048883) B1048883
theorem B699275 : Blo 698317 699275 := bstep (se 1 (by rfl) ⟨524456, by rfl⟩ : syracuseStep 699275 = 1048913) B1048913
theorem B699287 : Blo 698317 699287 := bstep (se 1 (by rfl) ⟨524465, by rfl⟩ : syracuseStep 699287 = 1048931) B1048931
theorem B699307 : Blo 698317 699307 := bstep (se 1 (by rfl) ⟨524480, by rfl⟩ : syracuseStep 699307 = 1048961) B1048961
theorem B699319 : Blo 698317 699319 := bstep (se 1 (by rfl) ⟨524489, by rfl⟩ : syracuseStep 699319 = 1048979) B1048979
theorem B699339 : Blo 698317 699339 := bstep (se 1 (by rfl) ⟨524504, by rfl⟩ : syracuseStep 699339 = 1049009) B1049009
theorem B699351 : Blo 698317 699351 := bstep (se 1 (by rfl) ⟨524513, by rfl⟩ : syracuseStep 699351 = 1049027) B1049027
theorem B699371 : Blo 698317 699371 := bstep (se 1 (by rfl) ⟨524528, by rfl⟩ : syracuseStep 699371 = 1049057) B1049057
theorem B699383 : Blo 698317 699383 := bstep (se 1 (by rfl) ⟨524537, by rfl⟩ : syracuseStep 699383 = 1049075) B1049075
theorem B699403 : Blo 698317 699403 := bstep (se 1 (by rfl) ⟨524552, by rfl⟩ : syracuseStep 699403 = 1049105) B1049105
theorem B699415 : Blo 698317 699415 := bstep (se 1 (by rfl) ⟨524561, by rfl⟩ : syracuseStep 699415 = 1049123) B1049123
theorem B699435 : Blo 698317 699435 := bstep (se 1 (by rfl) ⟨524576, by rfl⟩ : syracuseStep 699435 = 1049153) B1049153
theorem B699447 : Blo 698317 699447 := bstep (se 1 (by rfl) ⟨524585, by rfl⟩ : syracuseStep 699447 = 1049171) B1049171
theorem B699467 : Blo 698317 699467 := bstep (se 1 (by rfl) ⟨524600, by rfl⟩ : syracuseStep 699467 = 1049201) B1049201
theorem B5319755 : Blo 698317 5319755 := bstep (se 1 (by rfl) ⟨3989816, by rfl⟩ : syracuseStep 5319755 = 7979633) B7979633
theorem B699479 : Blo 698317 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B699499 : Blo 698317 699499 := bstep (se 1 (by rfl) ⟨524624, by rfl⟩ : syracuseStep 699499 = 1049249) B1049249
theorem B699511 : Blo 698317 699511 := bstep (se 1 (by rfl) ⟨524633, by rfl⟩ : syracuseStep 699511 = 1049267) B1049267
theorem B699531 : Blo 698317 699531 := bstep (se 1 (by rfl) ⟨524648, by rfl⟩ : syracuseStep 699531 = 1049297) B1049297
theorem B699543 : Blo 698317 699543 := bstep (se 1 (by rfl) ⟨524657, by rfl⟩ : syracuseStep 699543 = 1049315) B1049315
theorem B699563 : Blo 698317 699563 := bstep (se 1 (by rfl) ⟨524672, by rfl⟩ : syracuseStep 699563 = 1049345) B1049345
theorem B699575 : Blo 698317 699575 := bstep (se 1 (by rfl) ⟨524681, by rfl⟩ : syracuseStep 699575 = 1049363) B1049363
theorem B699595 : Blo 698317 699595 := bstep (se 1 (by rfl) ⟨524696, by rfl⟩ : syracuseStep 699595 = 1049393) B1049393
theorem B699607 : Blo 698317 699607 := bstep (se 1 (by rfl) ⟨524705, by rfl⟩ : syracuseStep 699607 = 1049411) B1049411
theorem B699627 : Blo 698317 699627 := bstep (se 1 (by rfl) ⟨524720, by rfl⟩ : syracuseStep 699627 = 1049441) B1049441
theorem B699639 : Blo 698317 699639 := bstep (se 1 (by rfl) ⟨524729, by rfl⟩ : syracuseStep 699639 = 1049459) B1049459
theorem B699659 : Blo 698317 699659 := bstep (se 1 (by rfl) ⟨524744, by rfl⟩ : syracuseStep 699659 = 1049489) B1049489
theorem B699671 : Blo 698317 699671 := bstep (se 1 (by rfl) ⟨524753, by rfl⟩ : syracuseStep 699671 = 1049507) B1049507
theorem B699691 : Blo 698317 699691 := bstep (se 1 (by rfl) ⟨524768, by rfl⟩ : syracuseStep 699691 = 1049537) B1049537
theorem B699703 : Blo 698317 699703 := bstep (se 1 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 699703 = 1049555) B1049555
theorem B699723 : Blo 698317 699723 := bstep (se 1 (by rfl) ⟨524792, by rfl⟩ : syracuseStep 699723 = 1049585) B1049585
theorem B699735 : Blo 698317 699735 := bstep (se 1 (by rfl) ⟨524801, by rfl⟩ : syracuseStep 699735 = 1049603) B1049603
theorem B2665817 : Blo 698317 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B699755 : Blo 698317 699755 := bstep (se 1 (by rfl) ⟨524816, by rfl⟩ : syracuseStep 699755 = 1049633) B1049633
theorem B699767 : Blo 698317 699767 := bstep (se 1 (by rfl) ⟨524825, by rfl⟩ : syracuseStep 699767 = 1049651) B1049651
theorem B699787 : Blo 698317 699787 := bstep (se 1 (by rfl) ⟨524840, by rfl⟩ : syracuseStep 699787 = 1049681) B1049681
theorem B699799 : Blo 698317 699799 := bstep (se 1 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 699799 = 1049699) B1049699
theorem B699819 : Blo 698317 699819 := bstep (se 1 (by rfl) ⟨524864, by rfl⟩ : syracuseStep 699819 = 1049729) B1049729
theorem B699831 : Blo 698317 699831 := bstep (se 1 (by rfl) ⟨524873, by rfl⟩ : syracuseStep 699831 = 1049747) B1049747
theorem B699851 : Blo 698317 699851 := bstep (se 1 (by rfl) ⟨524888, by rfl⟩ : syracuseStep 699851 = 1049777) B1049777
theorem B699863 : Blo 698317 699863 := bstep (se 1 (by rfl) ⟨524897, by rfl⟩ : syracuseStep 699863 = 1049795) B1049795
theorem B699883 : Blo 698317 699883 := bstep (se 1 (by rfl) ⟨524912, by rfl⟩ : syracuseStep 699883 = 1049825) B1049825
theorem B699895 : Blo 698317 699895 := bstep (se 1 (by rfl) ⟨524921, by rfl⟩ : syracuseStep 699895 = 1049843) B1049843
theorem B699915 : Blo 698317 699915 := bstep (se 1 (by rfl) ⟨524936, by rfl⟩ : syracuseStep 699915 = 1049873) B1049873
theorem B699927 : Blo 698317 699927 := bstep (se 1 (by rfl) ⟨524945, by rfl⟩ : syracuseStep 699927 = 1049891) B1049891
theorem B699947 : Blo 698317 699947 := bstep (se 1 (by rfl) ⟨524960, by rfl⟩ : syracuseStep 699947 = 1049921) B1049921
theorem B699959 : Blo 698317 699959 := bstep (se 1 (by rfl) ⟨524969, by rfl⟩ : syracuseStep 699959 = 1049939) B1049939
theorem B699979 : Blo 698317 699979 := bstep (se 1 (by rfl) ⟨524984, by rfl⟩ : syracuseStep 699979 = 1049969) B1049969
theorem B699991 : Blo 698317 699991 := bstep (se 1 (by rfl) ⟨524993, by rfl⟩ : syracuseStep 699991 = 1049987) B1049987
theorem B700011 : Blo 698317 700011 := bstep (se 1 (by rfl) ⟨525008, by rfl⟩ : syracuseStep 700011 = 1050017) B1050017
theorem B700023 : Blo 698317 700023 := bstep (se 1 (by rfl) ⟨525017, by rfl⟩ : syracuseStep 700023 = 1050035) B1050035
theorem B700043 : Blo 698317 700043 := bstep (se 1 (by rfl) ⟨525032, by rfl⟩ : syracuseStep 700043 = 1050065) B1050065
theorem B700055 : Blo 698317 700055 := bstep (se 1 (by rfl) ⟨525041, by rfl⟩ : syracuseStep 700055 = 1050083) B1050083
theorem B2666135 : Blo 698317 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B700075 : Blo 698317 700075 := bstep (se 1 (by rfl) ⟨525056, by rfl⟩ : syracuseStep 700075 = 1050113) B1050113
theorem B700087 : Blo 698317 700087 := bstep (se 1 (by rfl) ⟨525065, by rfl⟩ : syracuseStep 700087 = 1050131) B1050131
theorem B700107 : Blo 698317 700107 := bstep (se 1 (by rfl) ⟨525080, by rfl⟩ : syracuseStep 700107 = 1050161) B1050161
theorem B2993867 : Blo 698317 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B700119 : Blo 698317 700119 := bstep (se 1 (by rfl) ⟨525089, by rfl⟩ : syracuseStep 700119 = 1050179) B1050179
theorem B700139 : Blo 698317 700139 := bstep (se 1 (by rfl) ⟨525104, by rfl⟩ : syracuseStep 700139 = 1050209) B1050209
theorem B700151 : Blo 698317 700151 := bstep (se 1 (by rfl) ⟨525113, by rfl⟩ : syracuseStep 700151 = 1050227) B1050227
theorem B700171 : Blo 698317 700171 := bstep (se 1 (by rfl) ⟨525128, by rfl⟩ : syracuseStep 700171 = 1050257) B1050257
theorem B700183 : Blo 698317 700183 := bstep (se 1 (by rfl) ⟨525137, by rfl⟩ : syracuseStep 700183 = 1050275) B1050275
theorem B1421081 : Blo 698317 1421081 := bstep (se 2 (by rfl) ⟨532905, by rfl⟩ : syracuseStep 1421081 = 1065811) B1065811
theorem B700203 : Blo 698317 700203 := bstep (se 1 (by rfl) ⟨525152, by rfl⟩ : syracuseStep 700203 = 1050305) B1050305
theorem B700215 : Blo 698317 700215 := bstep (se 1 (by rfl) ⟨525161, by rfl⟩ : syracuseStep 700215 = 1050323) B1050323
theorem B700235 : Blo 698317 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B700247 : Blo 698317 700247 := bstep (se 1 (by rfl) ⟨525185, by rfl⟩ : syracuseStep 700247 = 1050371) B1050371
theorem B700267 : Blo 698317 700267 := bstep (se 1 (by rfl) ⟨525200, by rfl⟩ : syracuseStep 700267 = 1050401) B1050401
theorem B700279 : Blo 698317 700279 := bstep (se 1 (by rfl) ⟨525209, by rfl⟩ : syracuseStep 700279 = 1050419) B1050419
theorem B700299 : Blo 698317 700299 := bstep (se 1 (by rfl) ⟨525224, by rfl⟩ : syracuseStep 700299 = 1050449) B1050449
theorem B700311 : Blo 698317 700311 := bstep (se 1 (by rfl) ⟨525233, by rfl⟩ : syracuseStep 700311 = 1050467) B1050467
theorem B700331 : Blo 698317 700331 := bstep (se 1 (by rfl) ⟨525248, by rfl⟩ : syracuseStep 700331 = 1050497) B1050497
theorem B700343 : Blo 698317 700343 := bstep (se 1 (by rfl) ⟨525257, by rfl⟩ : syracuseStep 700343 = 1050515) B1050515
theorem B700363 : Blo 698317 700363 := bstep (se 1 (by rfl) ⟨525272, by rfl⟩ : syracuseStep 700363 = 1050545) B1050545
theorem B700375 : Blo 698317 700375 := bstep (se 1 (by rfl) ⟨525281, by rfl⟩ : syracuseStep 700375 = 1050563) B1050563
theorem B700395 : Blo 698317 700395 := bstep (se 1 (by rfl) ⟨525296, by rfl⟩ : syracuseStep 700395 = 1050593) B1050593
theorem B700407 : Blo 698317 700407 := bstep (se 1 (by rfl) ⟨525305, by rfl⟩ : syracuseStep 700407 = 1050611) B1050611
theorem B700427 : Blo 698317 700427 := bstep (se 1 (by rfl) ⟨525320, by rfl⟩ : syracuseStep 700427 = 1050641) B1050641
theorem B700439 : Blo 698317 700439 := bstep (se 1 (by rfl) ⟨525329, by rfl⟩ : syracuseStep 700439 = 1050659) B1050659
theorem B700459 : Blo 698317 700459 := bstep (se 1 (by rfl) ⟨525344, by rfl⟩ : syracuseStep 700459 = 1050689) B1050689
theorem B700471 : Blo 698317 700471 := bstep (se 1 (by rfl) ⟨525353, by rfl⟩ : syracuseStep 700471 = 1050707) B1050707
theorem B700491 : Blo 698317 700491 := bstep (se 1 (by rfl) ⟨525368, by rfl⟩ : syracuseStep 700491 = 1050737) B1050737
theorem B700503 : Blo 698317 700503 := bstep (se 1 (by rfl) ⟨525377, by rfl⟩ : syracuseStep 700503 = 1050755) B1050755
theorem B700523 : Blo 698317 700523 := bstep (se 1 (by rfl) ⟨525392, by rfl⟩ : syracuseStep 700523 = 1050785) B1050785
theorem B700535 : Blo 698317 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B3551363 : Blo 698317 3551363 := bstep (se 1 (by rfl) ⟨2663522, by rfl⟩ : syracuseStep 3551363 = 5327045) B5327045
theorem B700555 : Blo 698317 700555 := bstep (se 1 (by rfl) ⟨525416, by rfl⟩ : syracuseStep 700555 = 1050833) B1050833
theorem B700567 : Blo 698317 700567 := bstep (se 1 (by rfl) ⟨525425, by rfl⟩ : syracuseStep 700567 = 1050851) B1050851
theorem B700587 : Blo 698317 700587 := bstep (se 1 (by rfl) ⟨525440, by rfl⟩ : syracuseStep 700587 = 1050881) B1050881
theorem B700599 : Blo 698317 700599 := bstep (se 1 (by rfl) ⟨525449, by rfl⟩ : syracuseStep 700599 = 1050899) B1050899
theorem B700619 : Blo 698317 700619 := bstep (se 1 (by rfl) ⟨525464, by rfl⟩ : syracuseStep 700619 = 1050929) B1050929
theorem B700631 : Blo 698317 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B700651 : Blo 698317 700651 := bstep (se 1 (by rfl) ⟨525488, by rfl⟩ : syracuseStep 700651 = 1050977) B1050977
theorem B700663 : Blo 698317 700663 := bstep (se 1 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 700663 = 1050995) B1050995
theorem B700683 : Blo 698317 700683 := bstep (se 1 (by rfl) ⟨525512, by rfl⟩ : syracuseStep 700683 = 1051025) B1051025
theorem B700695 : Blo 698317 700695 := bstep (se 1 (by rfl) ⟨525521, by rfl⟩ : syracuseStep 700695 = 1051043) B1051043
theorem B995609 : Blo 698317 995609 := bstep (se 2 (by rfl) ⟨373353, by rfl⟩ : syracuseStep 995609 = 746707) B746707
theorem B700715 : Blo 698317 700715 := bstep (se 1 (by rfl) ⟨525536, by rfl⟩ : syracuseStep 700715 = 1051073) B1051073
theorem B700727 : Blo 698317 700727 := bstep (se 1 (by rfl) ⟨525545, by rfl⟩ : syracuseStep 700727 = 1051091) B1051091
theorem B700747 : Blo 698317 700747 := bstep (se 1 (by rfl) ⟨525560, by rfl⟩ : syracuseStep 700747 = 1051121) B1051121
theorem B700759 : Blo 698317 700759 := bstep (se 1 (by rfl) ⟨525569, by rfl⟩ : syracuseStep 700759 = 1051139) B1051139
theorem B700779 : Blo 698317 700779 := bstep (se 1 (by rfl) ⟨525584, by rfl⟩ : syracuseStep 700779 = 1051169) B1051169
theorem B700791 : Blo 698317 700791 := bstep (se 1 (by rfl) ⟨525593, by rfl⟩ : syracuseStep 700791 = 1051187) B1051187
theorem B700811 : Blo 698317 700811 := bstep (se 1 (by rfl) ⟨525608, by rfl⟩ : syracuseStep 700811 = 1051217) B1051217
theorem B700823 : Blo 698317 700823 := bstep (se 1 (by rfl) ⟨525617, by rfl⟩ : syracuseStep 700823 = 1051235) B1051235
theorem B700843 : Blo 698317 700843 := bstep (se 1 (by rfl) ⟨525632, by rfl⟩ : syracuseStep 700843 = 1051265) B1051265
theorem B700855 : Blo 698317 700855 := bstep (se 1 (by rfl) ⟨525641, by rfl⟩ : syracuseStep 700855 = 1051283) B1051283
theorem B1421761 : Blo 698317 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B700875 : Blo 698317 700875 := bstep (se 1 (by rfl) ⟨525656, by rfl⟩ : syracuseStep 700875 = 1051313) B1051313
theorem B700887 : Blo 698317 700887 := bstep (se 1 (by rfl) ⟨525665, by rfl⟩ : syracuseStep 700887 = 1051331) B1051331
theorem B2699741 : Blo 698317 2699741 := bstep (se 3 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 2699741 = 1012403) B1012403
theorem B700907 : Blo 698317 700907 := bstep (se 1 (by rfl) ⟨525680, by rfl⟩ : syracuseStep 700907 = 1051361) B1051361
theorem B700919 : Blo 698317 700919 := bstep (se 1 (by rfl) ⟨525689, by rfl⟩ : syracuseStep 700919 = 1051379) B1051379
theorem B700939 : Blo 698317 700939 := bstep (se 1 (by rfl) ⟨525704, by rfl⟩ : syracuseStep 700939 = 1051409) B1051409
theorem B700951 : Blo 698317 700951 := bstep (se 1 (by rfl) ⟨525713, by rfl⟩ : syracuseStep 700951 = 1051427) B1051427
theorem B700971 : Blo 698317 700971 := bstep (se 1 (by rfl) ⟨525728, by rfl⟩ : syracuseStep 700971 = 1051457) B1051457
theorem B700983 : Blo 698317 700983 := bstep (se 1 (by rfl) ⟨525737, by rfl⟩ : syracuseStep 700983 = 1051475) B1051475
theorem B701003 : Blo 698317 701003 := bstep (se 1 (by rfl) ⟨525752, by rfl⟩ : syracuseStep 701003 = 1051505) B1051505
theorem B701015 : Blo 698317 701015 := bstep (se 1 (by rfl) ⟨525761, by rfl⟩ : syracuseStep 701015 = 1051523) B1051523
theorem B701035 : Blo 698317 701035 := bstep (se 1 (by rfl) ⟨525776, by rfl⟩ : syracuseStep 701035 = 1051553) B1051553
theorem B701047 : Blo 698317 701047 := bstep (se 1 (by rfl) ⟨525785, by rfl⟩ : syracuseStep 701047 = 1051571) B1051571
theorem B701067 : Blo 698317 701067 := bstep (se 1 (by rfl) ⟨525800, by rfl⟩ : syracuseStep 701067 = 1051601) B1051601
theorem B701079 : Blo 698317 701079 := bstep (se 1 (by rfl) ⟨525809, by rfl⟩ : syracuseStep 701079 = 1051619) B1051619
theorem B701099 : Blo 698317 701099 := bstep (se 1 (by rfl) ⟨525824, by rfl⟩ : syracuseStep 701099 = 1051649) B1051649
theorem B701111 : Blo 698317 701111 := bstep (se 1 (by rfl) ⟨525833, by rfl⟩ : syracuseStep 701111 = 1051667) B1051667
theorem B701131 : Blo 698317 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B701143 : Blo 698317 701143 := bstep (se 1 (by rfl) ⟨525857, by rfl⟩ : syracuseStep 701143 = 1051715) B1051715
theorem B701163 : Blo 698317 701163 := bstep (se 1 (by rfl) ⟨525872, by rfl⟩ : syracuseStep 701163 = 1051745) B1051745
theorem B701175 : Blo 698317 701175 := bstep (se 1 (by rfl) ⟨525881, by rfl⟩ : syracuseStep 701175 = 1051763) B1051763
theorem B701195 : Blo 698317 701195 := bstep (se 1 (by rfl) ⟨525896, by rfl⟩ : syracuseStep 701195 = 1051793) B1051793
theorem B701207 : Blo 698317 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B701227 : Blo 698317 701227 := bstep (se 1 (by rfl) ⟨525920, by rfl⟩ : syracuseStep 701227 = 1051841) B1051841
theorem B2994995 : Blo 698317 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B701239 : Blo 698317 701239 := bstep (se 1 (by rfl) ⟨525929, by rfl⟩ : syracuseStep 701239 = 1051859) B1051859
theorem B701259 : Blo 698317 701259 := bstep (se 1 (by rfl) ⟨525944, by rfl⟩ : syracuseStep 701259 = 1051889) B1051889
theorem B701271 : Blo 698317 701271 := bstep (se 1 (by rfl) ⟨525953, by rfl⟩ : syracuseStep 701271 = 1051907) B1051907
theorem B5059421 : Blo 698317 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B701291 : Blo 698317 701291 := bstep (se 1 (by rfl) ⟨525968, by rfl⟩ : syracuseStep 701291 = 1051937) B1051937
theorem B701303 : Blo 698317 701303 := bstep (se 1 (by rfl) ⟨525977, by rfl⟩ : syracuseStep 701303 = 1051955) B1051955
theorem B701323 : Blo 698317 701323 := bstep (se 1 (by rfl) ⟨525992, by rfl⟩ : syracuseStep 701323 = 1051985) B1051985
theorem B996247 : Blo 698317 996247 := bstep (se 1 (by rfl) ⟨747185, by rfl⟩ : syracuseStep 996247 = 1494371) B1494371
theorem B701335 : Blo 698317 701335 := bstep (se 1 (by rfl) ⟨526001, by rfl⟩ : syracuseStep 701335 = 1052003) B1052003
theorem B701355 : Blo 698317 701355 := bstep (se 1 (by rfl) ⟨526016, by rfl⟩ : syracuseStep 701355 = 1052033) B1052033
theorem B701367 : Blo 698317 701367 := bstep (se 1 (by rfl) ⟨526025, by rfl⟩ : syracuseStep 701367 = 1052051) B1052051
theorem B701387 : Blo 698317 701387 := bstep (se 1 (by rfl) ⟨526040, by rfl⟩ : syracuseStep 701387 = 1052081) B1052081
theorem B701399 : Blo 698317 701399 := bstep (se 1 (by rfl) ⟨526049, by rfl⟩ : syracuseStep 701399 = 1052099) B1052099
theorem B701419 : Blo 698317 701419 := bstep (se 1 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 701419 = 1052129) B1052129
theorem B701431 : Blo 698317 701431 := bstep (se 1 (by rfl) ⟨526073, by rfl⟩ : syracuseStep 701431 = 1052147) B1052147
theorem B701451 : Blo 698317 701451 := bstep (se 1 (by rfl) ⟨526088, by rfl⟩ : syracuseStep 701451 = 1052177) B1052177
theorem B701463 : Blo 698317 701463 := bstep (se 1 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 701463 = 1052195) B1052195
theorem B701483 : Blo 698317 701483 := bstep (se 1 (by rfl) ⟨526112, by rfl⟩ : syracuseStep 701483 = 1052225) B1052225
theorem B701495 : Blo 698317 701495 := bstep (se 1 (by rfl) ⟨526121, by rfl⟩ : syracuseStep 701495 = 1052243) B1052243
theorem B701515 : Blo 698317 701515 := bstep (se 1 (by rfl) ⟨526136, by rfl⟩ : syracuseStep 701515 = 1052273) B1052273
theorem B701527 : Blo 698317 701527 := bstep (se 1 (by rfl) ⟨526145, by rfl⟩ : syracuseStep 701527 = 1052291) B1052291
theorem B701547 : Blo 698317 701547 := bstep (se 1 (by rfl) ⟨526160, by rfl⟩ : syracuseStep 701547 = 1052321) B1052321
theorem B701559 : Blo 698317 701559 := bstep (se 1 (by rfl) ⟨526169, by rfl⟩ : syracuseStep 701559 = 1052339) B1052339
theorem B701579 : Blo 698317 701579 := bstep (se 1 (by rfl) ⟨526184, by rfl⟩ : syracuseStep 701579 = 1052369) B1052369
theorem B701591 : Blo 698317 701591 := bstep (se 1 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 701591 = 1052387) B1052387
theorem B701611 : Blo 698317 701611 := bstep (se 1 (by rfl) ⟨526208, by rfl⟩ : syracuseStep 701611 = 1052417) B1052417
theorem B701623 : Blo 698317 701623 := bstep (se 1 (by rfl) ⟨526217, by rfl⟩ : syracuseStep 701623 = 1052435) B1052435
theorem B701643 : Blo 698317 701643 := bstep (se 1 (by rfl) ⟨526232, by rfl⟩ : syracuseStep 701643 = 1052465) B1052465
theorem B701655 : Blo 698317 701655 := bstep (se 1 (by rfl) ⟨526241, by rfl⟩ : syracuseStep 701655 = 1052483) B1052483
theorem B701675 : Blo 698317 701675 := bstep (se 1 (by rfl) ⟨526256, by rfl⟩ : syracuseStep 701675 = 1052513) B1052513
theorem B701687 : Blo 698317 701687 := bstep (se 1 (by rfl) ⟨526265, by rfl⟩ : syracuseStep 701687 = 1052531) B1052531
theorem B701707 : Blo 698317 701707 := bstep (se 1 (by rfl) ⟨526280, by rfl⟩ : syracuseStep 701707 = 1052561) B1052561
theorem B701719 : Blo 698317 701719 := bstep (se 1 (by rfl) ⟨526289, by rfl⟩ : syracuseStep 701719 = 1052579) B1052579
theorem B701739 : Blo 698317 701739 := bstep (se 1 (by rfl) ⟨526304, by rfl⟩ : syracuseStep 701739 = 1052609) B1052609
theorem B701751 : Blo 698317 701751 := bstep (se 1 (by rfl) ⟨526313, by rfl⟩ : syracuseStep 701751 = 1052627) B1052627
theorem B701771 : Blo 698317 701771 := bstep (se 1 (by rfl) ⟨526328, by rfl⟩ : syracuseStep 701771 = 1052657) B1052657
theorem B701783 : Blo 698317 701783 := bstep (se 1 (by rfl) ⟨526337, by rfl⟩ : syracuseStep 701783 = 1052675) B1052675
theorem B701803 : Blo 698317 701803 := bstep (se 1 (by rfl) ⟨526352, by rfl⟩ : syracuseStep 701803 = 1052705) B1052705
theorem B701815 : Blo 698317 701815 := bstep (se 1 (by rfl) ⟨526361, by rfl⟩ : syracuseStep 701815 = 1052723) B1052723
theorem B701835 : Blo 698317 701835 := bstep (se 1 (by rfl) ⟨526376, by rfl⟩ : syracuseStep 701835 = 1052753) B1052753
theorem B701847 : Blo 698317 701847 := bstep (se 1 (by rfl) ⟨526385, by rfl⟩ : syracuseStep 701847 = 1052771) B1052771
theorem B701867 : Blo 698317 701867 := bstep (se 1 (by rfl) ⟨526400, by rfl⟩ : syracuseStep 701867 = 1052801) B1052801
theorem B8959409 : Blo 698317 8959409 := bstep (se 2 (by rfl) ⟨3359778, by rfl⟩ : syracuseStep 8959409 = 6719557) B6719557
theorem B701879 : Blo 698317 701879 := bstep (se 1 (by rfl) ⟨526409, by rfl⟩ : syracuseStep 701879 = 1052819) B1052819
theorem B701899 : Blo 698317 701899 := bstep (se 1 (by rfl) ⟨526424, by rfl⟩ : syracuseStep 701899 = 1052849) B1052849
theorem B701911 : Blo 698317 701911 := bstep (se 1 (by rfl) ⟨526433, by rfl⟩ : syracuseStep 701911 = 1052867) B1052867
theorem B701931 : Blo 698317 701931 := bstep (se 1 (by rfl) ⟨526448, by rfl⟩ : syracuseStep 701931 = 1052897) B1052897
theorem B701943 : Blo 698317 701943 := bstep (se 1 (by rfl) ⟨526457, by rfl⟩ : syracuseStep 701943 = 1052915) B1052915
theorem B701963 : Blo 698317 701963 := bstep (se 1 (by rfl) ⟨526472, by rfl⟩ : syracuseStep 701963 = 1052945) B1052945
theorem B701975 : Blo 698317 701975 := bstep (se 1 (by rfl) ⟨526481, by rfl⟩ : syracuseStep 701975 = 1052963) B1052963
theorem B701995 : Blo 698317 701995 := bstep (se 1 (by rfl) ⟨526496, by rfl⟩ : syracuseStep 701995 = 1052993) B1052993
theorem B1259059 : Blo 698317 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B702007 : Blo 698317 702007 := bstep (se 1 (by rfl) ⟨526505, by rfl⟩ : syracuseStep 702007 = 1053011) B1053011
theorem B702027 : Blo 698317 702027 := bstep (se 1 (by rfl) ⟨526520, by rfl⟩ : syracuseStep 702027 = 1053041) B1053041
theorem B702039 : Blo 698317 702039 := bstep (se 1 (by rfl) ⟨526529, by rfl⟩ : syracuseStep 702039 = 1053059) B1053059
theorem B996953 : Blo 698317 996953 := bstep (se 2 (by rfl) ⟨373857, by rfl⟩ : syracuseStep 996953 = 747715) B747715
theorem B21575261 : Blo 698317 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B702059 : Blo 698317 702059 := bstep (se 1 (by rfl) ⟨526544, by rfl⟩ : syracuseStep 702059 = 1053089) B1053089
theorem B702071 : Blo 698317 702071 := bstep (se 1 (by rfl) ⟨526553, by rfl⟩ : syracuseStep 702071 = 1053107) B1053107
theorem B702091 : Blo 698317 702091 := bstep (se 1 (by rfl) ⟨526568, by rfl⟩ : syracuseStep 702091 = 1053137) B1053137
theorem B702103 : Blo 698317 702103 := bstep (se 1 (by rfl) ⟨526577, by rfl⟩ : syracuseStep 702103 = 1053155) B1053155
theorem B702123 : Blo 698317 702123 := bstep (se 1 (by rfl) ⟨526592, by rfl⟩ : syracuseStep 702123 = 1053185) B1053185
theorem B702135 : Blo 698317 702135 := bstep (se 1 (by rfl) ⟨526601, by rfl⟩ : syracuseStep 702135 = 1053203) B1053203
theorem B34059973 : Blo 698317 34059973 := bstep (se 4 (by rfl) ⟨3193122, by rfl⟩ : syracuseStep 34059973 = 6386245) B6386245
theorem B997067 : Blo 698317 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B702155 : Blo 698317 702155 := bstep (se 1 (by rfl) ⟨526616, by rfl⟩ : syracuseStep 702155 = 1053233) B1053233
theorem B702167 : Blo 698317 702167 := bstep (se 1 (by rfl) ⟨526625, by rfl⟩ : syracuseStep 702167 = 1053251) B1053251
theorem B702187 : Blo 698317 702187 := bstep (se 1 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 702187 = 1053281) B1053281
theorem B702199 : Blo 698317 702199 := bstep (se 1 (by rfl) ⟨526649, by rfl⟩ : syracuseStep 702199 = 1053299) B1053299
theorem B702219 : Blo 698317 702219 := bstep (se 1 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 702219 = 1053329) B1053329
theorem B702231 : Blo 698317 702231 := bstep (se 1 (by rfl) ⟨526673, by rfl⟩ : syracuseStep 702231 = 1053347) B1053347
theorem B702251 : Blo 698317 702251 := bstep (se 1 (by rfl) ⟨526688, by rfl⟩ : syracuseStep 702251 = 1053377) B1053377
theorem B702263 : Blo 698317 702263 := bstep (se 1 (by rfl) ⟨526697, by rfl⟩ : syracuseStep 702263 = 1053395) B1053395
theorem B3356491 : Blo 698317 3356491 := bstep (se 1 (by rfl) ⟨2517368, by rfl⟩ : syracuseStep 3356491 = 5034737) B5034737
theorem B702283 : Blo 698317 702283 := bstep (se 1 (by rfl) ⟨526712, by rfl⟩ : syracuseStep 702283 = 1053425) B1053425
theorem B702295 : Blo 698317 702295 := bstep (se 1 (by rfl) ⟨526721, by rfl⟩ : syracuseStep 702295 = 1053443) B1053443
theorem B702315 : Blo 698317 702315 := bstep (se 1 (by rfl) ⟨526736, by rfl⟩ : syracuseStep 702315 = 1053473) B1053473
theorem B3356567 : Blo 698317 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B2832529 : Blo 698317 2832529 := bstep (se 2 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 2832529 = 2124397) B2124397
theorem B997591 : Blo 698317 997591 := bstep (se 1 (by rfl) ⟨748193, by rfl⟩ : syracuseStep 997591 = 1496387) B1496387
theorem B1423577 : Blo 698317 1423577 := bstep (se 2 (by rfl) ⟨533841, by rfl⟩ : syracuseStep 1423577 = 1067683) B1067683
theorem B48380273 : Blo 698317 48380273 := bstep (se 2 (by rfl) ⟨18142602, by rfl⟩ : syracuseStep 48380273 = 36285205) B36285205
theorem B3979793 : Blo 698317 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B2996909 : Blo 698317 2996909 := bstep (se 3 (by rfl) ⟨561920, by rfl⟩ : syracuseStep 2996909 = 1123841) B1123841
theorem B1325747 : Blo 698317 1325747 := bstep (se 1 (by rfl) ⟨994310, by rfl⟩ : syracuseStep 1325747 = 1988621) B1988621
theorem B1260299 : Blo 698317 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B1325899 : Blo 698317 1325899 := bstep (se 1 (by rfl) ⟨994424, by rfl⟩ : syracuseStep 1325899 = 1988849) B1988849
theorem B3980249 : Blo 698317 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B998411 : Blo 698317 998411 := bstep (se 1 (by rfl) ⟨748808, by rfl⟩ : syracuseStep 998411 = 1497617) B1497617
theorem B1260631 : Blo 698317 1260631 := bstep (se 1 (by rfl) ⟨945473, by rfl⟩ : syracuseStep 1260631 = 1890947) B1890947
theorem B1326233 : Blo 698317 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B2997593 : Blo 698317 2997593 := bstep (se 2 (by rfl) ⟨1124097, by rfl⟩ : syracuseStep 2997593 = 2248195) B2248195
theorem B10108451 : Blo 698317 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B3194585 : Blo 698317 3194585 := bstep (se 2 (by rfl) ⟨1197969, by rfl⟩ : syracuseStep 3194585 = 2395939) B2395939
theorem B3555089 : Blo 698317 3555089 := bstep (se 2 (by rfl) ⟨1333158, by rfl⟩ : syracuseStep 3555089 = 2666317) B2666317
theorem B1326871 : Blo 698317 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B1261337 : Blo 698317 1261337 := bstep (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) B946003
theorem B2277209 : Blo 698317 2277209 := bstep (se 2 (by rfl) ⟨853953, by rfl⟩ : syracuseStep 2277209 = 1707907) B1707907
theorem B3555251 : Blo 698317 3555251 := bstep (se 1 (by rfl) ⟨2666438, by rfl⟩ : syracuseStep 3555251 = 5332877) B5332877
theorem B2834507 : Blo 698317 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B1622155 : Blo 698317 1622155 := bstep (se 1 (by rfl) ⟨1216616, by rfl⟩ : syracuseStep 1622155 = 2433233) B2433233
theorem B2834635 : Blo 698317 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B5325101 : Blo 698317 5325101 := bstep (se 3 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 5325101 = 1996913) B1996913
theorem B1327691 : Blo 698317 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B2245195 : Blo 698317 2245195 := bstep (se 1 (by rfl) ⟨1683896, by rfl⟩ : syracuseStep 2245195 = 3367793) B3367793
theorem B1327745 : Blo 698317 1327745 := bstep (se 2 (by rfl) ⟨497904, by rfl⟩ : syracuseStep 1327745 = 995809) B995809
theorem B8077975 : Blo 698317 8077975 := bstep (se 1 (by rfl) ⟨6058481, by rfl⟩ : syracuseStep 8077975 = 12116963) B12116963
theorem B1262231 : Blo 698317 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B1491671 : Blo 698317 1491671 := bstep (se 1 (by rfl) ⟨1118753, by rfl⟩ : syracuseStep 1491671 = 2237507) B2237507
theorem B1196759 : Blo 698317 1196759 := bstep (se 1 (by rfl) ⟨897569, by rfl⟩ : syracuseStep 1196759 = 1795139) B1795139
theorem B2245427 : Blo 698317 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B26886977 : Blo 698317 26886977 := bstep (se 2 (by rfl) ⟨10082616, by rfl⟩ : syracuseStep 26886977 = 20165233) B20165233
theorem B1491979 : Blo 698317 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B11945393 : Blo 698317 11945393 := bstep (se 2 (by rfl) ⟨4479522, by rfl⟩ : syracuseStep 11945393 = 8959045) B8959045
theorem B1328663 : Blo 698317 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B10929815 : Blo 698317 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B1492825 : Blo 698317 1492825 := bstep (se 2 (by rfl) ⟨559809, by rfl⟩ : syracuseStep 1492825 = 1119619) B1119619
theorem B51136433 : Blo 698317 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B7981091 : Blo 698317 7981091 := bstep (se 1 (by rfl) ⟨5985818, by rfl⟩ : syracuseStep 7981091 = 11971637) B11971637
theorem B1329203 : Blo 698317 1329203 := bstep (se 1 (by rfl) ⟨996902, by rfl⟩ : syracuseStep 1329203 = 1993805) B1993805
theorem B1263961 : Blo 698317 1263961 := bstep (se 2 (by rfl) ⟨473985, by rfl⟩ : syracuseStep 1263961 = 947971) B947971
theorem B1329689 : Blo 698317 1329689 := bstep (se 2 (by rfl) ⟨498633, by rfl⟩ : syracuseStep 1329689 = 997267) B997267
theorem B1494131 : Blo 698317 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B839575 : Blo 698317 839575 := bstep (se 1 (by rfl) ⟨629681, by rfl⟩ : syracuseStep 839575 = 1259363) B1259363
theorem B1200023 : Blo 698317 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B1331147 : Blo 698317 1331147 := bstep (se 1 (by rfl) ⟨998360, by rfl⟩ : syracuseStep 1331147 = 1996721) B1996721
theorem B5689379 : Blo 698317 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B1200215 : Blo 698317 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B5328989 : Blo 698317 5328989 := bstep (se 3 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 5328989 = 1998371) B1998371
theorem B1331329 : Blo 698317 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B3985625 : Blo 698317 3985625 := bstep (se 2 (by rfl) ⟨1494609, by rfl⟩ : syracuseStep 3985625 = 2989219) B2989219
theorem B3232145 : Blo 698317 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B6738353 : Blo 698317 6738353 := bstep (se 2 (by rfl) ⟨2526882, by rfl⟩ : syracuseStep 6738353 = 5053765) B5053765
theorem B1331777 : Blo 698317 1331777 := bstep (se 2 (by rfl) ⟨499416, by rfl⟩ : syracuseStep 1331777 = 998833) B998833
theorem B1495703 : Blo 698317 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B6378371 : Blo 698317 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B1332119 : Blo 698317 1332119 := bstep (se 1 (by rfl) ⟨999089, by rfl⟩ : syracuseStep 1332119 = 1998179) B1998179
theorem B1496011 : Blo 698317 1496011 := bstep (se 1 (by rfl) ⟨1122008, by rfl⟩ : syracuseStep 1496011 = 2244017) B2244017
theorem B1332787 : Blo 698317 1332787 := bstep (se 1 (by rfl) ⟨999590, by rfl⟩ : syracuseStep 1332787 = 1999181) B1999181
theorem B3987265 : Blo 698317 3987265 := bstep (se 2 (by rfl) ⟨1495224, by rfl⟩ : syracuseStep 3987265 = 2990449) B2990449
theorem B3200843 : Blo 698317 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B1595315 : Blo 698317 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B1333235 : Blo 698317 1333235 := bstep (se 1 (by rfl) ⟨999926, by rfl⟩ : syracuseStep 1333235 = 1999853) B1999853
theorem B1333273 : Blo 698317 1333273 := bstep (se 2 (by rfl) ⟨499977, by rfl⟩ : syracuseStep 1333273 = 999955) B999955
theorem B87447605 : Blo 698317 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B1595467 : Blo 698317 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B1497241 : Blo 698317 1497241 := bstep (se 2 (by rfl) ⟨561465, by rfl⟩ : syracuseStep 1497241 = 1122931) B1122931
theorem B5691713 : Blo 698317 5691713 := bstep (se 2 (by rfl) ⟨2134392, by rfl⟩ : syracuseStep 5691713 = 4268785) B4268785
theorem B12114613 : Blo 698317 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B711659 : Blo 698317 711659 := bstep (se 1 (by rfl) ⟨533744, by rfl⟩ : syracuseStep 711659 = 1067489) B1067489
theorem B4545629 : Blo 698317 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B5037157 : Blo 698317 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B7560323 : Blo 698317 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B5987459 : Blo 698317 5987459 := bstep (se 1 (by rfl) ⟨4490594, by rfl⟩ : syracuseStep 5987459 = 8981189) B8981189
theorem B1597067 : Blo 698317 1597067 := bstep (se 1 (by rfl) ⟨1197800, by rfl⟩ : syracuseStep 1597067 = 2395601) B2395601
theorem B4251467 : Blo 698317 4251467 := bstep (se 1 (by rfl) ⟨3188600, by rfl⟩ : syracuseStep 4251467 = 6377201) B6377201
theorem B1990489 : Blo 698317 1990489 := bstep (se 2 (by rfl) ⟨746433, by rfl⟩ : syracuseStep 1990489 = 1492867) B1492867
theorem B4481345 : Blo 698317 4481345 := bstep (se 2 (by rfl) ⟨1680504, by rfl⟩ : syracuseStep 4481345 = 3361009) B3361009
theorem B1991105 : Blo 698317 1991105 := bstep (se 2 (by rfl) ⟨746664, by rfl⟩ : syracuseStep 1991105 = 1493329) B1493329
theorem B5038541 : Blo 698317 5038541 := bstep (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) B1889453
theorem B746263 : Blo 698317 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B15131717 : Blo 698317 15131717 := bstep (se 4 (by rfl) ⟨1418598, by rfl⟩ : syracuseStep 15131717 = 2837197) B2837197
theorem B3990707 : Blo 698317 3990707 := bstep (se 1 (by rfl) ⟨2993030, by rfl⟩ : syracuseStep 3990707 = 5986061) B5986061
theorem B747083 : Blo 698317 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B2516953 : Blo 698317 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B5990435 : Blo 698317 5990435 := bstep (se 1 (by rfl) ⟨4492826, by rfl⟩ : syracuseStep 5990435 = 8985653) B8985653
theorem B1993177 : Blo 698317 1993177 := bstep (se 2 (by rfl) ⟨747441, by rfl⟩ : syracuseStep 1993177 = 1494883) B1494883
theorem B1436161 : Blo 698317 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B2845277 : Blo 698317 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B3992165 : Blo 698317 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B748279 : Blo 698317 748279 := bstep (se 1 (by rfl) ⟨561209, by rfl⟩ : syracuseStep 748279 = 1122419) B1122419
theorem B3074861 : Blo 698317 3074861 := bstep (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) B1153073
theorem B1993565 : Blo 698317 1993565 := bstep (se 3 (by rfl) ⟨373793, by rfl⟩ : syracuseStep 1993565 = 747587) B747587
theorem B748535 : Blo 698317 748535 := bstep (se 1 (by rfl) ⟨561401, by rfl⟩ : syracuseStep 748535 = 1122803) B1122803
theorem B4779395 : Blo 698317 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B6712793 : Blo 698317 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B749099 : Blo 698317 749099 := bstep (se 1 (by rfl) ⟨561824, by rfl⟩ : syracuseStep 749099 = 1123649) B1123649
theorem B5762765 : Blo 698317 5762765 := bstep (se 3 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 5762765 = 2161037) B2161037
theorem B4255553 : Blo 698317 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B3371159 : Blo 698317 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B3371329 : Blo 698317 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B4485469 : Blo 698317 4485469 := bstep (se 3 (by rfl) ⟨841025, by rfl⟩ : syracuseStep 4485469 = 1682051) B1682051
theorem B20247245 : Blo 698317 20247245 := bstep (se 3 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 20247245 = 7592717) B7592717
theorem B2847577 : Blo 698317 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B7992755 : Blo 698317 7992755 := bstep (se 1 (by rfl) ⟨5994566, by rfl⟩ : syracuseStep 7992755 = 11989133) B11989133
theorem B1897931 : Blo 698317 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B2651723 : Blo 698317 2651723 := bstep (se 1 (by rfl) ⟨1988792, by rfl⟩ : syracuseStep 2651723 = 3977585) B3977585
theorem B3536459 : Blo 698317 3536459 := bstep (se 1 (by rfl) ⟨2652344, by rfl⟩ : syracuseStep 3536459 = 5304689) B5304689
theorem B2651737 : Blo 698317 2651737 := bstep (se 2 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 2651737 = 1988803) B1988803
theorem B2356829 : Blo 698317 2356829 := bstep (se 3 (by rfl) ⟨441905, by rfl⟩ : syracuseStep 2356829 = 883811) B883811
theorem B1996481 : Blo 698317 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B26965709 : Blo 698317 26965709 := bstep (se 3 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 26965709 = 10112141) B10112141
theorem B947927 : Blo 698317 947927 := bstep (se 1 (by rfl) ⟨710945, by rfl⟩ : syracuseStep 947927 = 1421891) B1421891
theorem B5306147 : Blo 698317 5306147 := bstep (se 1 (by rfl) ⟨3979610, by rfl⟩ : syracuseStep 5306147 = 7959221) B7959221
theorem B1996595 : Blo 698317 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B6387673 : Blo 698317 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B2521219 : Blo 698317 2521219 := bstep (se 1 (by rfl) ⟨1890914, by rfl⟩ : syracuseStep 2521219 = 3781829) B3781829
theorem B1767703 : Blo 698317 1767703 := bstep (se 1 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 1767703 = 2651555) B2651555
theorem B2652695 : Blo 698317 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B1571417 : Blo 698317 1571417 := bstep (se 2 (by rfl) ⟨589281, by rfl⟩ : syracuseStep 1571417 = 1178563) B1178563
theorem B1571507 : Blo 698317 1571507 := bstep (se 1 (by rfl) ⟨1178630, by rfl⟩ : syracuseStep 1571507 = 2357261) B2357261
theorem B1768139 : Blo 698317 1768139 := bstep (se 1 (by rfl) ⟨1326104, by rfl⟩ : syracuseStep 1768139 = 2652209) B2652209
theorem B2357963 : Blo 698317 2357963 := bstep (se 1 (by rfl) ⟨1768472, by rfl⟩ : syracuseStep 2357963 = 3536945) B3536945
theorem B1571543 : Blo 698317 1571543 := bstep (se 1 (by rfl) ⟨1178657, by rfl⟩ : syracuseStep 1571543 = 2357315) B2357315
theorem B1178455 : Blo 698317 1178455 := bstep (se 1 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 1178455 = 1767683) B1767683
theorem B7994213 : Blo 698317 7994213 := bstep (se 4 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 7994213 = 1498915) B1498915
theorem B1571723 : Blo 698317 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B1571777 : Blo 698317 1571777 := bstep (se 2 (by rfl) ⟨589416, by rfl⟩ : syracuseStep 1571777 = 1178833) B1178833
theorem B2358233 : Blo 698317 2358233 := bstep (se 2 (by rfl) ⟨884337, by rfl⟩ : syracuseStep 2358233 = 1768675) B1768675
theorem B1047563 : Blo 698317 1047563 := bstep (se 1 (by rfl) ⟨785672, by rfl⟩ : syracuseStep 1047563 = 1571345) B1571345
theorem B1047575 : Blo 698317 1047575 := bstep (se 1 (by rfl) ⟨785681, by rfl⟩ : syracuseStep 1047575 = 1571363) B1571363
theorem B1768513 : Blo 698317 1768513 := bstep (se 2 (by rfl) ⟨663192, by rfl⟩ : syracuseStep 1768513 = 1326385) B1326385
theorem B1047641 : Blo 698317 1047641 := bstep (se 2 (by rfl) ⟨392865, by rfl⟩ : syracuseStep 1047641 = 785731) B785731
theorem B1571993 : Blo 698317 1571993 := bstep (se 2 (by rfl) ⟨589497, by rfl⟩ : syracuseStep 1571993 = 1178995) B1178995
theorem B1047755 : Blo 698317 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B785623 : Blo 698317 785623 := bstep (se 1 (by rfl) ⟨589217, by rfl⟩ : syracuseStep 785623 = 1178435) B1178435
theorem B1047767 : Blo 698317 1047767 := bstep (se 1 (by rfl) ⟨785825, by rfl⟩ : syracuseStep 1047767 = 1571651) B1571651
theorem B1572083 : Blo 698317 1572083 := bstep (se 1 (by rfl) ⟨1179062, by rfl⟩ : syracuseStep 1572083 = 2358125) B2358125
theorem B1572119 : Blo 698317 1572119 := bstep (se 1 (by rfl) ⟨1179089, by rfl⟩ : syracuseStep 1572119 = 2358179) B2358179
theorem B1047833 : Blo 698317 1047833 := bstep (se 2 (by rfl) ⟨392937, by rfl⟩ : syracuseStep 1047833 = 785875) B785875
theorem B3538241 : Blo 698317 3538241 := bstep (se 2 (by rfl) ⟨1326840, by rfl⟩ : syracuseStep 3538241 = 2653681) B2653681
theorem B2522443 : Blo 698317 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B785803 : Blo 698317 785803 := bstep (se 1 (by rfl) ⟨589352, by rfl⟩ : syracuseStep 785803 = 1178705) B1178705
theorem B1047947 : Blo 698317 1047947 := bstep (se 1 (by rfl) ⟨785960, by rfl⟩ : syracuseStep 1047947 = 1571921) B1571921
theorem B1047959 : Blo 698317 1047959 := bstep (se 1 (by rfl) ⟨785969, by rfl⟩ : syracuseStep 1047959 = 1571939) B1571939
theorem B5766551 : Blo 698317 5766551 := bstep (se 1 (by rfl) ⟨4324913, by rfl⟩ : syracuseStep 5766551 = 8649827) B8649827
theorem B1179083 : Blo 698317 1179083 := bstep (se 1 (by rfl) ⟨884312, by rfl⟩ : syracuseStep 1179083 = 1768625) B1768625
theorem B1572299 : Blo 698317 1572299 := bstep (se 1 (by rfl) ⟨1179224, by rfl⟩ : syracuseStep 1572299 = 2358449) B2358449
theorem B1048025 : Blo 698317 1048025 := bstep (se 2 (by rfl) ⟨393009, by rfl⟩ : syracuseStep 1048025 = 786019) B786019
theorem B785911 : Blo 698317 785911 := bstep (se 1 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 785911 = 1178867) B1178867
theorem B1572353 : Blo 698317 1572353 := bstep (se 2 (by rfl) ⟨589632, by rfl⟩ : syracuseStep 1572353 = 1179265) B1179265
theorem B1048139 : Blo 698317 1048139 := bstep (se 1 (by rfl) ⟨786104, by rfl⟩ : syracuseStep 1048139 = 1572209) B1572209
theorem B1179211 : Blo 698317 1179211 := bstep (se 1 (by rfl) ⟨884408, by rfl⟩ : syracuseStep 1179211 = 1768817) B1768817
theorem B1048151 : Blo 698317 1048151 := bstep (se 1 (by rfl) ⟨786113, by rfl⟩ : syracuseStep 1048151 = 1572227) B1572227
theorem B1769111 : Blo 698317 1769111 := bstep (se 1 (by rfl) ⟨1326833, by rfl⟩ : syracuseStep 1769111 = 2653667) B2653667
theorem B2358935 : Blo 698317 2358935 := bstep (se 1 (by rfl) ⟨1769201, by rfl⟩ : syracuseStep 2358935 = 3538403) B3538403
theorem B1048217 : Blo 698317 1048217 := bstep (se 2 (by rfl) ⟨393081, by rfl⟩ : syracuseStep 1048217 = 786163) B786163
theorem B786091 : Blo 698317 786091 := bstep (se 1 (by rfl) ⟨589568, by rfl⟩ : syracuseStep 786091 = 1179137) B1179137
theorem B1179353 : Blo 698317 1179353 := bstep (se 2 (by rfl) ⟨442257, by rfl⟩ : syracuseStep 1179353 = 884515) B884515
theorem B1572569 : Blo 698317 1572569 := bstep (se 2 (by rfl) ⟨589713, by rfl⟩ : syracuseStep 1572569 = 1179427) B1179427
theorem B2653955 : Blo 698317 2653955 := bstep (se 1 (by rfl) ⟨1990466, by rfl⟩ : syracuseStep 2653955 = 3980933) B3980933
theorem B1048331 : Blo 698317 1048331 := bstep (se 1 (by rfl) ⟨786248, by rfl⟩ : syracuseStep 1048331 = 1572497) B1572497
theorem B786199 : Blo 698317 786199 := bstep (se 1 (by rfl) ⟨589649, by rfl⟩ : syracuseStep 786199 = 1179299) B1179299
theorem B1048343 : Blo 698317 1048343 := bstep (se 1 (by rfl) ⟨786257, by rfl⟩ : syracuseStep 1048343 = 1572515) B1572515
theorem B1572659 : Blo 698317 1572659 := bstep (se 1 (by rfl) ⟨1179494, by rfl⟩ : syracuseStep 1572659 = 2358989) B2358989
theorem B1572695 : Blo 698317 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B1048409 : Blo 698317 1048409 := bstep (se 2 (by rfl) ⟨393153, by rfl⟩ : syracuseStep 1048409 = 786307) B786307
theorem B1179481 : Blo 698317 1179481 := bstep (se 2 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 1179481 = 884611) B884611
theorem B786379 : Blo 698317 786379 := bstep (se 1 (by rfl) ⟨589784, by rfl⟩ : syracuseStep 786379 = 1179569) B1179569
theorem B1048523 : Blo 698317 1048523 := bstep (se 1 (by rfl) ⟨786392, by rfl⟩ : syracuseStep 1048523 = 1572785) B1572785
theorem B1048535 : Blo 698317 1048535 := bstep (se 1 (by rfl) ⟨786401, by rfl⟩ : syracuseStep 1048535 = 1572803) B1572803
theorem B1048583 : Blo 698317 1048583 := bstep (se 1 (by rfl) ⟨786437, by rfl⟩ : syracuseStep 1048583 = 1572875) B1572875
theorem B1048619 : Blo 698317 1048619 := bstep (se 1 (by rfl) ⟨786464, by rfl⟩ : syracuseStep 1048619 = 1572929) B1572929
theorem B1048649 : Blo 698317 1048649 := bstep (se 2 (by rfl) ⟨393243, by rfl⟩ : syracuseStep 1048649 = 786487) B786487
theorem B1572983 : Blo 698317 1572983 := bstep (se 1 (by rfl) ⟨1179737, by rfl⟩ : syracuseStep 1572983 = 2359475) B2359475
theorem B2162873 : Blo 698317 2162873 := bstep (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) B1622155
theorem B1048763 : Blo 698317 1048763 := bstep (se 1 (by rfl) ⟨786572, by rfl⟩ : syracuseStep 1048763 = 1573145) B1573145
theorem B1048823 : Blo 698317 1048823 := bstep (se 1 (by rfl) ⟨786617, by rfl⟩ : syracuseStep 1048823 = 1573235) B1573235
theorem B1048847 : Blo 698317 1048847 := bstep (se 1 (by rfl) ⟨786635, by rfl⟩ : syracuseStep 1048847 = 1573271) B1573271
theorem B786703 : Blo 698317 786703 := bstep (se 1 (by rfl) ⟨590027, by rfl⟩ : syracuseStep 786703 = 1180055) B1180055
theorem B1573163 : Blo 698317 1573163 := bstep (se 1 (by rfl) ⟨1179872, by rfl⟩ : syracuseStep 1573163 = 2359745) B2359745
theorem B1179947 : Blo 698317 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B1048889 : Blo 698317 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B1048967 : Blo 698317 1048967 := bstep (se 1 (by rfl) ⟨786725, by rfl⟩ : syracuseStep 1048967 = 1573451) B1573451
theorem B1049003 : Blo 698317 1049003 := bstep (se 1 (by rfl) ⟨786752, by rfl⟩ : syracuseStep 1049003 = 1573505) B1573505
theorem B885163 : Blo 698317 885163 := bstep (se 1 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 885163 = 1327745) B1327745
theorem B1049033 : Blo 698317 1049033 := bstep (se 2 (by rfl) ⟨393387, by rfl⟩ : syracuseStep 1049033 = 786775) B786775
theorem B17924651 : Blo 698317 17924651 := bstep (se 1 (by rfl) ⟨13443488, by rfl⟩ : syracuseStep 17924651 = 26886977) B26886977
theorem B932774453 : Blo 698317 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B1049147 : Blo 698317 1049147 := bstep (se 1 (by rfl) ⟨786860, by rfl⟩ : syracuseStep 1049147 = 1573721) B1573721
theorem B1049207 : Blo 698317 1049207 := bstep (se 1 (by rfl) ⟨786905, by rfl⟩ : syracuseStep 1049207 = 1573811) B1573811
theorem B1049231 : Blo 698317 1049231 := bstep (se 1 (by rfl) ⟨786923, by rfl⟩ : syracuseStep 1049231 = 1573847) B1573847
theorem B1573523 : Blo 698317 1573523 := bstep (se 1 (by rfl) ⟨1180142, by rfl⟩ : syracuseStep 1573523 = 2360285) B2360285
theorem B7570097 : Blo 698317 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B1180345 : Blo 698317 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B1049273 : Blo 698317 1049273 := bstep (se 2 (by rfl) ⟨393477, by rfl⟩ : syracuseStep 1049273 = 786955) B786955
theorem B1573577 : Blo 698317 1573577 := bstep (se 2 (by rfl) ⟨590091, by rfl⟩ : syracuseStep 1573577 = 1180183) B1180183
theorem B2654957 : Blo 698317 2654957 := bstep (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) B995609
theorem B1049351 : Blo 698317 1049351 := bstep (se 1 (by rfl) ⟨787013, by rfl⟩ : syracuseStep 1049351 = 1574027) B1574027
theorem B787207 : Blo 698317 787207 := bstep (se 1 (by rfl) ⟨590405, by rfl⟩ : syracuseStep 787207 = 1180811) B1180811
theorem B1049387 : Blo 698317 1049387 := bstep (se 1 (by rfl) ⟨787040, by rfl⟩ : syracuseStep 1049387 = 1574081) B1574081
theorem B2360123 : Blo 698317 2360123 := bstep (se 1 (by rfl) ⟨1770092, by rfl⟩ : syracuseStep 2360123 = 3540185) B3540185
theorem B1049417 : Blo 698317 1049417 := bstep (se 2 (by rfl) ⟨393531, by rfl⟩ : syracuseStep 1049417 = 787063) B787063
theorem B1049531 : Blo 698317 1049531 := bstep (se 1 (by rfl) ⟨787148, by rfl⟩ : syracuseStep 1049531 = 1574297) B1574297
theorem B787387 : Blo 698317 787387 := bstep (se 1 (by rfl) ⟨590540, by rfl⟩ : syracuseStep 787387 = 1181081) B1181081
theorem B7963595 : Blo 698317 7963595 := bstep (se 1 (by rfl) ⟨5972696, by rfl⟩ : syracuseStep 7963595 = 11945393) B11945393
theorem B1049591 : Blo 698317 1049591 := bstep (se 1 (by rfl) ⟨787193, by rfl⟩ : syracuseStep 1049591 = 1574387) B1574387
theorem B1049615 : Blo 698317 1049615 := bstep (se 1 (by rfl) ⟨787211, by rfl⟩ : syracuseStep 1049615 = 1574423) B1574423
theorem B1049657 : Blo 698317 1049657 := bstep (se 2 (by rfl) ⟨393621, by rfl⟩ : syracuseStep 1049657 = 787243) B787243
theorem B1049735 : Blo 698317 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B1049771 : Blo 698317 1049771 := bstep (se 1 (by rfl) ⟨787328, by rfl⟩ : syracuseStep 1049771 = 1574657) B1574657
theorem B1049801 : Blo 698317 1049801 := bstep (se 2 (by rfl) ⟨393675, by rfl⟩ : syracuseStep 1049801 = 787351) B787351
theorem B2360609 : Blo 698317 2360609 := bstep (se 2 (by rfl) ⟨885228, by rfl⟩ : syracuseStep 2360609 = 1770457) B1770457
theorem B1049915 : Blo 698317 1049915 := bstep (se 1 (by rfl) ⟨787436, by rfl⟩ : syracuseStep 1049915 = 1574873) B1574873
theorem B1181047 : Blo 698317 1181047 := bstep (se 1 (by rfl) ⟨885785, by rfl⟩ : syracuseStep 1181047 = 1771571) B1771571
theorem B1049975 : Blo 698317 1049975 := bstep (se 1 (by rfl) ⟨787481, by rfl⟩ : syracuseStep 1049975 = 1574963) B1574963
theorem B886135 : Blo 698317 886135 := bstep (se 1 (by rfl) ⟨664601, by rfl⟩ : syracuseStep 886135 = 1329203) B1329203
theorem B1574279 : Blo 698317 1574279 := bstep (se 1 (by rfl) ⟨1180709, by rfl⟩ : syracuseStep 1574279 = 2361419) B2361419
theorem B1049999 : Blo 698317 1049999 := bstep (se 1 (by rfl) ⟨787499, by rfl⟩ : syracuseStep 1049999 = 1574999) B1574999
theorem B787855 : Blo 698317 787855 := bstep (se 1 (by rfl) ⟨590891, by rfl⟩ : syracuseStep 787855 = 1181783) B1181783
theorem B1050041 : Blo 698317 1050041 := bstep (se 2 (by rfl) ⟨393765, by rfl⟩ : syracuseStep 1050041 = 787531) B787531
theorem B1050119 : Blo 698317 1050119 := bstep (se 1 (by rfl) ⟨787589, by rfl⟩ : syracuseStep 1050119 = 1575179) B1575179
theorem B3540509 : Blo 698317 3540509 := bstep (se 3 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 3540509 = 1327691) B1327691
theorem B2885149 : Blo 698317 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B1050155 : Blo 698317 1050155 := bstep (se 1 (by rfl) ⟨787616, by rfl⟩ : syracuseStep 1050155 = 1575233) B1575233
theorem B1574459 : Blo 698317 1574459 := bstep (se 1 (by rfl) ⟨1180844, by rfl⟩ : syracuseStep 1574459 = 2361689) B2361689
theorem B1181243 : Blo 698317 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B1050185 : Blo 698317 1050185 := bstep (se 2 (by rfl) ⟨393819, by rfl⟩ : syracuseStep 1050185 = 787639) B787639
theorem B1574585 : Blo 698317 1574585 := bstep (se 2 (by rfl) ⟨590469, by rfl⟩ : syracuseStep 1574585 = 1180939) B1180939
theorem B1050299 : Blo 698317 1050299 := bstep (se 1 (by rfl) ⟨787724, by rfl⟩ : syracuseStep 1050299 = 1575449) B1575449
theorem B886459 : Blo 698317 886459 := bstep (se 1 (by rfl) ⟨664844, by rfl⟩ : syracuseStep 886459 = 1329689) B1329689
theorem B1050359 : Blo 698317 1050359 := bstep (se 1 (by rfl) ⟨787769, by rfl⟩ : syracuseStep 1050359 = 1575539) B1575539
theorem B1050383 : Blo 698317 1050383 := bstep (se 1 (by rfl) ⟨787787, by rfl⟩ : syracuseStep 1050383 = 1575575) B1575575
theorem B1050425 : Blo 698317 1050425 := bstep (se 2 (by rfl) ⟨393909, by rfl⟩ : syracuseStep 1050425 = 787819) B787819
theorem B2361203 : Blo 698317 2361203 := bstep (se 1 (by rfl) ⟨1770902, by rfl⟩ : syracuseStep 2361203 = 3541805) B3541805
theorem B1771379 : Blo 698317 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B1050503 : Blo 698317 1050503 := bstep (se 1 (by rfl) ⟨787877, by rfl⟩ : syracuseStep 1050503 = 1575755) B1575755
theorem B788359 : Blo 698317 788359 := bstep (se 1 (by rfl) ⟨591269, by rfl⟩ : syracuseStep 788359 = 1182539) B1182539
theorem B1050539 : Blo 698317 1050539 := bstep (se 1 (by rfl) ⟨787904, by rfl⟩ : syracuseStep 1050539 = 1575809) B1575809
theorem B1181641 : Blo 698317 1181641 := bstep (se 2 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 1181641 = 886231) B886231
theorem B1050569 : Blo 698317 1050569 := bstep (se 2 (by rfl) ⟨393963, by rfl⟩ : syracuseStep 1050569 = 787927) B787927
theorem B3540995 : Blo 698317 3540995 := bstep (se 1 (by rfl) ⟨2655746, by rfl⟩ : syracuseStep 3540995 = 5311493) B5311493
theorem B1574927 : Blo 698317 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B1574945 : Blo 698317 1574945 := bstep (se 2 (by rfl) ⟨590604, by rfl⟩ : syracuseStep 1574945 = 1181209) B1181209
theorem B1050683 : Blo 698317 1050683 := bstep (se 1 (by rfl) ⟨788012, by rfl⟩ : syracuseStep 1050683 = 1576025) B1576025
theorem B788539 : Blo 698317 788539 := bstep (se 1 (by rfl) ⟨591404, by rfl⟩ : syracuseStep 788539 = 1182809) B1182809
theorem B1050743 : Blo 698317 1050743 := bstep (se 1 (by rfl) ⟨788057, by rfl⟩ : syracuseStep 1050743 = 1576115) B1576115
theorem B1050767 : Blo 698317 1050767 := bstep (se 1 (by rfl) ⟨788075, by rfl⟩ : syracuseStep 1050767 = 1576151) B1576151
theorem B1050809 : Blo 698317 1050809 := bstep (se 2 (by rfl) ⟨394053, by rfl⟩ : syracuseStep 1050809 = 788107) B788107
theorem B4327625 : Blo 698317 4327625 := bstep (se 2 (by rfl) ⟨1622859, by rfl⟩ : syracuseStep 4327625 = 3245719) B3245719
theorem B1050887 : Blo 698317 1050887 := bstep (se 1 (by rfl) ⟨788165, by rfl⟩ : syracuseStep 1050887 = 1576331) B1576331
theorem B1050923 : Blo 698317 1050923 := bstep (se 1 (by rfl) ⟨788192, by rfl⟩ : syracuseStep 1050923 = 1576385) B1576385
theorem B1050953 : Blo 698317 1050953 := bstep (se 2 (by rfl) ⟨394107, by rfl⟩ : syracuseStep 1050953 = 788215) B788215
theorem B1771895 : Blo 698317 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B1575287 : Blo 698317 1575287 := bstep (se 1 (by rfl) ⟨1181465, by rfl⟩ : syracuseStep 1575287 = 2362931) B2362931
theorem B1051067 : Blo 698317 1051067 := bstep (se 1 (by rfl) ⟨788300, by rfl⟩ : syracuseStep 1051067 = 1576601) B1576601
theorem B1051127 : Blo 698317 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B1051151 : Blo 698317 1051151 := bstep (se 1 (by rfl) ⟨788363, by rfl⟩ : syracuseStep 1051151 = 1576727) B1576727
theorem B789007 : Blo 698317 789007 := bstep (se 1 (by rfl) ⟨591755, by rfl⟩ : syracuseStep 789007 = 1183511) B1183511
theorem B1575467 : Blo 698317 1575467 := bstep (se 1 (by rfl) ⟨1181600, by rfl⟩ : syracuseStep 1575467 = 2363201) B2363201
theorem B1051193 : Blo 698317 1051193 := bstep (se 2 (by rfl) ⟨394197, by rfl⟩ : syracuseStep 1051193 = 788395) B788395
theorem B887431 : Blo 698317 887431 := bstep (se 1 (by rfl) ⟨665573, by rfl⟩ : syracuseStep 887431 = 1331147) B1331147
theorem B1182343 : Blo 698317 1182343 := bstep (se 1 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 1182343 = 1773515) B1773515
theorem B1051271 : Blo 698317 1051271 := bstep (se 1 (by rfl) ⟨788453, by rfl⟩ : syracuseStep 1051271 = 1576907) B1576907
theorem B1051307 : Blo 698317 1051307 := bstep (se 1 (by rfl) ⟨788480, by rfl⟩ : syracuseStep 1051307 = 1576961) B1576961
theorem B1051337 : Blo 698317 1051337 := bstep (se 2 (by rfl) ⟨394251, by rfl⟩ : syracuseStep 1051337 = 788503) B788503
theorem B2657083 : Blo 698317 2657083 := bstep (se 1 (by rfl) ⟨1992812, by rfl⟩ : syracuseStep 2657083 = 3985625) B3985625
theorem B1051451 : Blo 698317 1051451 := bstep (se 1 (by rfl) ⟨788588, by rfl⟩ : syracuseStep 1051451 = 1577177) B1577177
theorem B4787059 : Blo 698317 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B1051511 : Blo 698317 1051511 := bstep (se 1 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 1051511 = 1577267) B1577267
theorem B1051535 : Blo 698317 1051535 := bstep (se 1 (by rfl) ⟨788651, by rfl⟩ : syracuseStep 1051535 = 1577303) B1577303
theorem B1575827 : Blo 698317 1575827 := bstep (se 1 (by rfl) ⟨1181870, by rfl⟩ : syracuseStep 1575827 = 2363741) B2363741
theorem B1051577 : Blo 698317 1051577 := bstep (se 2 (by rfl) ⟨394341, by rfl⟩ : syracuseStep 1051577 = 788683) B788683
theorem B1575881 : Blo 698317 1575881 := bstep (se 2 (by rfl) ⟨590955, by rfl⟩ : syracuseStep 1575881 = 1181911) B1181911
theorem B4492235 : Blo 698317 4492235 := bstep (se 1 (by rfl) ⟨3369176, by rfl⟩ : syracuseStep 4492235 = 6738353) B6738353
theorem B1051655 : Blo 698317 1051655 := bstep (se 1 (by rfl) ⟨788741, by rfl⟩ : syracuseStep 1051655 = 1577483) B1577483
theorem B789511 : Blo 698317 789511 := bstep (se 1 (by rfl) ⟨592133, by rfl⟩ : syracuseStep 789511 = 1184267) B1184267
theorem B1051691 : Blo 698317 1051691 := bstep (se 1 (by rfl) ⟨788768, by rfl⟩ : syracuseStep 1051691 = 1577537) B1577537
theorem B887851 : Blo 698317 887851 := bstep (se 1 (by rfl) ⟨665888, by rfl⟩ : syracuseStep 887851 = 1331777) B1331777
theorem B1051721 : Blo 698317 1051721 := bstep (se 2 (by rfl) ⟨394395, by rfl⟩ : syracuseStep 1051721 = 788791) B788791
theorem B1051835 : Blo 698317 1051835 := bstep (se 1 (by rfl) ⟨788876, by rfl⟩ : syracuseStep 1051835 = 1577753) B1577753
theorem B789691 : Blo 698317 789691 := bstep (se 1 (by rfl) ⟨592268, by rfl⟩ : syracuseStep 789691 = 1184537) B1184537
theorem B1051895 : Blo 698317 1051895 := bstep (se 1 (by rfl) ⟨788921, by rfl⟩ : syracuseStep 1051895 = 1577843) B1577843
theorem B1182991 : Blo 698317 1182991 := bstep (se 1 (by rfl) ⟨887243, by rfl⟩ : syracuseStep 1182991 = 1774487) B1774487
theorem B1051919 : Blo 698317 1051919 := bstep (se 1 (by rfl) ⟨788939, by rfl⟩ : syracuseStep 1051919 = 1577879) B1577879
theorem B888079 : Blo 698317 888079 := bstep (se 1 (by rfl) ⟨666059, by rfl⟩ : syracuseStep 888079 = 1332119) B1332119
theorem B2657569 : Blo 698317 2657569 := bstep (se 2 (by rfl) ⟨996588, by rfl⟩ : syracuseStep 2657569 = 1993177) B1993177
theorem B1051961 : Blo 698317 1051961 := bstep (se 2 (by rfl) ⟨394485, by rfl⟩ : syracuseStep 1051961 = 788971) B788971
theorem B1772887 : Blo 698317 1772887 := bstep (se 1 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 1772887 = 2659331) B2659331
theorem B1052039 : Blo 698317 1052039 := bstep (se 1 (by rfl) ⟨789029, by rfl⟩ : syracuseStep 1052039 = 1578059) B1578059
theorem B1052075 : Blo 698317 1052075 := bstep (se 1 (by rfl) ⟨789056, by rfl⟩ : syracuseStep 1052075 = 1578113) B1578113
theorem B1052105 : Blo 698317 1052105 := bstep (se 2 (by rfl) ⟨394539, by rfl⟩ : syracuseStep 1052105 = 789079) B789079
theorem B1052219 : Blo 698317 1052219 := bstep (se 1 (by rfl) ⟨789164, by rfl⟩ : syracuseStep 1052219 = 1578329) B1578329
theorem B3542615 : Blo 698317 3542615 := bstep (se 1 (by rfl) ⟨2656961, by rfl⟩ : syracuseStep 3542615 = 5313923) B5313923
theorem B4263511 : Blo 698317 4263511 := bstep (se 1 (by rfl) ⟨3197633, by rfl⟩ : syracuseStep 4263511 = 6395267) B6395267
theorem B1052279 : Blo 698317 1052279 := bstep (se 1 (by rfl) ⟨789209, by rfl⟩ : syracuseStep 1052279 = 1578419) B1578419
theorem B1773191 : Blo 698317 1773191 := bstep (se 1 (by rfl) ⟨1329893, by rfl⟩ : syracuseStep 1773191 = 2659787) B2659787
theorem B1576583 : Blo 698317 1576583 := bstep (se 1 (by rfl) ⟨1182437, by rfl⟩ : syracuseStep 1576583 = 2364875) B2364875
theorem B1052303 : Blo 698317 1052303 := bstep (se 1 (by rfl) ⟨789227, by rfl⟩ : syracuseStep 1052303 = 1578455) B1578455
theorem B1052345 : Blo 698317 1052345 := bstep (se 2 (by rfl) ⟨394629, by rfl⟩ : syracuseStep 1052345 = 789259) B789259
theorem B14946049 : Blo 698317 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B54529793 : Blo 698317 54529793 := bstep (se 2 (by rfl) ⟨20448672, by rfl⟩ : syracuseStep 54529793 = 40897345) B40897345
theorem B1052423 : Blo 698317 1052423 := bstep (se 1 (by rfl) ⟨789317, by rfl⟩ : syracuseStep 1052423 = 1578635) B1578635
theorem B1773323 : Blo 698317 1773323 := bstep (se 1 (by rfl) ⟨1329992, by rfl⟩ : syracuseStep 1773323 = 2659985) B2659985
theorem B1183531 : Blo 698317 1183531 := bstep (se 1 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 1183531 = 1775297) B1775297
theorem B1052459 : Blo 698317 1052459 := bstep (se 1 (by rfl) ⟨789344, by rfl⟩ : syracuseStep 1052459 = 1578689) B1578689
theorem B1576763 : Blo 698317 1576763 := bstep (se 1 (by rfl) ⟨1182572, by rfl⟩ : syracuseStep 1576763 = 2365145) B2365145
theorem B1052489 : Blo 698317 1052489 := bstep (se 2 (by rfl) ⟨394683, by rfl⟩ : syracuseStep 1052489 = 789367) B789367
theorem B1576889 : Blo 698317 1576889 := bstep (se 2 (by rfl) ⟨591333, by rfl⟩ : syracuseStep 1576889 = 1182667) B1182667
theorem B1183673 : Blo 698317 1183673 := bstep (se 2 (by rfl) ⟨443877, by rfl⟩ : syracuseStep 1183673 = 887755) B887755
theorem B1052603 : Blo 698317 1052603 := bstep (se 1 (by rfl) ⟨789452, by rfl⟩ : syracuseStep 1052603 = 1578905) B1578905
theorem B1052663 : Blo 698317 1052663 := bstep (se 1 (by rfl) ⟨789497, by rfl⟩ : syracuseStep 1052663 = 1578995) B1578995
theorem B888823 : Blo 698317 888823 := bstep (se 1 (by rfl) ⟨666617, by rfl⟩ : syracuseStep 888823 = 1333235) B1333235
theorem B1052687 : Blo 698317 1052687 := bstep (se 1 (by rfl) ⟨789515, by rfl⟩ : syracuseStep 1052687 = 1579031) B1579031
theorem B1052729 : Blo 698317 1052729 := bstep (se 2 (by rfl) ⟨394773, by rfl⟩ : syracuseStep 1052729 = 789547) B789547
theorem B3543101 : Blo 698317 3543101 := bstep (se 3 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 3543101 = 1328663) B1328663
theorem B1052807 : Blo 698317 1052807 := bstep (se 1 (by rfl) ⟨789605, by rfl⟩ : syracuseStep 1052807 = 1579211) B1579211
theorem B1052843 : Blo 698317 1052843 := bstep (se 1 (by rfl) ⟨789632, by rfl⟩ : syracuseStep 1052843 = 1579265) B1579265
theorem B1052873 : Blo 698317 1052873 := bstep (se 2 (by rfl) ⟨394827, by rfl⟩ : syracuseStep 1052873 = 789655) B789655
theorem B2658541 : Blo 698317 2658541 := bstep (se 3 (by rfl) ⟨498476, by rfl⟩ : syracuseStep 2658541 = 996953) B996953
theorem B1773839 : Blo 698317 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B1577231 : Blo 698317 1577231 := bstep (se 1 (by rfl) ⟨1182923, by rfl⟩ : syracuseStep 1577231 = 2365847) B2365847
theorem B1577249 : Blo 698317 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B5968187 : Blo 698317 5968187 := bstep (se 1 (by rfl) ⟨4476140, by rfl⟩ : syracuseStep 5968187 = 8952281) B8952281
theorem B1052987 : Blo 698317 1052987 := bstep (se 1 (by rfl) ⟨789740, by rfl⟩ : syracuseStep 1052987 = 1579481) B1579481
theorem B1053047 : Blo 698317 1053047 := bstep (se 1 (by rfl) ⟨789785, by rfl⟩ : syracuseStep 1053047 = 1579571) B1579571
theorem B1053071 : Blo 698317 1053071 := bstep (se 1 (by rfl) ⟨789803, by rfl⟩ : syracuseStep 1053071 = 1579607) B1579607
theorem B2363795 : Blo 698317 2363795 := bstep (se 1 (by rfl) ⟨1772846, by rfl⟩ : syracuseStep 2363795 = 3545693) B3545693
theorem B1773971 : Blo 698317 1773971 := bstep (se 1 (by rfl) ⟨1330478, by rfl⟩ : syracuseStep 1773971 = 2660957) B2660957
theorem B1053113 : Blo 698317 1053113 := bstep (se 2 (by rfl) ⟨394917, by rfl⟩ : syracuseStep 1053113 = 789835) B789835
theorem B1053191 : Blo 698317 1053191 := bstep (se 1 (by rfl) ⟨789893, by rfl⟩ : syracuseStep 1053191 = 1579787) B1579787
theorem B2658845 : Blo 698317 2658845 := bstep (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) B997067
theorem B1053227 : Blo 698317 1053227 := bstep (se 1 (by rfl) ⟨789920, by rfl⟩ : syracuseStep 1053227 = 1579841) B1579841
theorem B2527805 : Blo 698317 2527805 := bstep (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) B947927
theorem B1053257 : Blo 698317 1053257 := bstep (se 2 (by rfl) ⟨394971, by rfl⟩ : syracuseStep 1053257 = 789943) B789943
theorem B1577591 : Blo 698317 1577591 := bstep (se 1 (by rfl) ⟨1183193, by rfl⟩ : syracuseStep 1577591 = 2366387) B2366387
theorem B1184375 : Blo 698317 1184375 := bstep (se 1 (by rfl) ⟨888281, by rfl⟩ : syracuseStep 1184375 = 1776563) B1776563
theorem B1053371 : Blo 698317 1053371 := bstep (se 1 (by rfl) ⟨790028, by rfl⟩ : syracuseStep 1053371 = 1580057) B1580057
theorem B1053431 : Blo 698317 1053431 := bstep (se 1 (by rfl) ⟨790073, by rfl⟩ : syracuseStep 1053431 = 1580147) B1580147
theorem B4789007 : Blo 698317 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B1053455 : Blo 698317 1053455 := bstep (se 1 (by rfl) ⟨790091, by rfl⟩ : syracuseStep 1053455 = 1580183) B1580183
theorem B1577771 : Blo 698317 1577771 := bstep (se 1 (by rfl) ⟨1183328, by rfl⟩ : syracuseStep 1577771 = 2366657) B2366657
theorem B1708919 : Blo 698317 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B1184827 : Blo 698317 1184827 := bstep (se 1 (by rfl) ⟨888620, by rfl⟩ : syracuseStep 1184827 = 1777241) B1777241
theorem B1578131 : Blo 698317 1578131 := bstep (se 1 (by rfl) ⟨1183598, by rfl⟩ : syracuseStep 1578131 = 2367197) B2367197
theorem B1119433 : Blo 698317 1119433 := bstep (se 2 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 1119433 = 839575) B839575
theorem B1578185 : Blo 698317 1578185 := bstep (se 2 (by rfl) ⟨591819, by rfl⟩ : syracuseStep 1578185 = 1183639) B1183639
theorem B1184969 : Blo 698317 1184969 := bstep (se 2 (by rfl) ⟨444363, by rfl⟩ : syracuseStep 1184969 = 888727) B888727
theorem B1775105 : Blo 698317 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B2987563 : Blo 698317 2987563 := bstep (se 1 (by rfl) ⟨2240672, by rfl⟩ : syracuseStep 2987563 = 4481345) B4481345
theorem B4495105 : Blo 698317 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B2365199 : Blo 698317 2365199 := bstep (se 1 (by rfl) ⟨1773899, by rfl⟩ : syracuseStep 2365199 = 3547799) B3547799
theorem B3544883 : Blo 698317 3544883 := bstep (se 1 (by rfl) ⟨2658662, by rfl⟩ : syracuseStep 3544883 = 5317325) B5317325
theorem B1775479 : Blo 698317 1775479 := bstep (se 1 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 1775479 = 2663219) B2663219
theorem B1578887 : Blo 698317 1578887 := bstep (se 1 (by rfl) ⟨1184165, by rfl⟩ : syracuseStep 1578887 = 2368331) B2368331
theorem B2365469 : Blo 698317 2365469 := bstep (se 3 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 2365469 = 887051) B887051
theorem B1579067 : Blo 698317 1579067 := bstep (se 1 (by rfl) ⟨1184300, by rfl⟩ : syracuseStep 1579067 = 2368601) B2368601
theorem B3545207 : Blo 698317 3545207 := bstep (se 1 (by rfl) ⟨2658905, by rfl⟩ : syracuseStep 3545207 = 5317811) B5317811
theorem B2660471 : Blo 698317 2660471 := bstep (se 1 (by rfl) ⟨1995353, by rfl⟩ : syracuseStep 2660471 = 3990707) B3990707
theorem B15177901 : Blo 698317 15177901 := bstep (se 3 (by rfl) ⟨2845856, by rfl⟩ : syracuseStep 15177901 = 5691713) B5691713
theorem B1579193 : Blo 698317 1579193 := bstep (se 2 (by rfl) ⟨592197, by rfl⟩ : syracuseStep 1579193 = 1184395) B1184395
theorem B1775915 : Blo 698317 1775915 := bstep (se 1 (by rfl) ⟨1331936, by rfl⟩ : syracuseStep 1775915 = 2663873) B2663873
theorem B1579535 : Blo 698317 1579535 := bstep (se 1 (by rfl) ⟨1184651, by rfl⟩ : syracuseStep 1579535 = 2369303) B2369303
theorem B1579553 : Blo 698317 1579553 := bstep (se 2 (by rfl) ⟨592332, by rfl⟩ : syracuseStep 1579553 = 1184665) B1184665
theorem B1579895 : Blo 698317 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B1580075 : Blo 698317 1580075 := bstep (se 1 (by rfl) ⟨1185056, by rfl⟩ : syracuseStep 1580075 = 2370113) B2370113
theorem B3546179 : Blo 698317 3546179 := bstep (se 1 (by rfl) ⟨2659634, by rfl⟩ : syracuseStep 3546179 = 5319269) B5319269
theorem B2661443 : Blo 698317 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B1776755 : Blo 698317 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B1776775 : Blo 698317 1776775 := bstep (se 1 (by rfl) ⟨1332581, by rfl⟩ : syracuseStep 1776775 = 2665163) B2665163
theorem B3546503 : Blo 698317 3546503 := bstep (se 1 (by rfl) ⟨2659877, by rfl⟩ : syracuseStep 3546503 = 5319755) B5319755
theorem B1678745 : Blo 698317 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B2366873 : Blo 698317 2366873 := bstep (se 2 (by rfl) ⟨887577, by rfl⟩ : syracuseStep 2366873 = 1775155) B1775155
theorem B1777049 : Blo 698317 1777049 := bstep (se 2 (by rfl) ⟨666393, by rfl⟩ : syracuseStep 1777049 = 1332787) B1332787
theorem B1973705 : Blo 698317 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B1777211 : Blo 698317 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B3186263 : Blo 698317 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B5316353 : Blo 698317 5316353 := bstep (se 2 (by rfl) ⟨1993632, by rfl⟩ : syracuseStep 5316353 = 3987265) B3987265
theorem B1777423 : Blo 698317 1777423 := bstep (se 1 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 1777423 = 2666135) B2666135
theorem B3841843 : Blo 698317 3841843 := bstep (se 1 (by rfl) ⟨2881382, by rfl⟩ : syracuseStep 3841843 = 5762765) B5762765
theorem B2662429 : Blo 698317 2662429 := bstep (se 3 (by rfl) ⟨499205, by rfl⟩ : syracuseStep 2662429 = 998411) B998411
theorem B1777697 : Blo 698317 1777697 := bstep (se 2 (by rfl) ⟨666636, by rfl⟩ : syracuseStep 1777697 = 1333273) B1333273
theorem B2367575 : Blo 698317 2367575 := bstep (se 1 (by rfl) ⟨1775681, by rfl⟩ : syracuseStep 2367575 = 3551363) B3551363
theorem B3776705 : Blo 698317 3776705 := bstep (se 2 (by rfl) ⟨1416264, by rfl⟩ : syracuseStep 3776705 = 2832529) B2832529
theorem B25960981 : Blo 698317 25960981 := bstep (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) B1216921
theorem B2990621 : Blo 698317 2990621 := bstep (se 3 (by rfl) ⟨560741, by rfl⟩ : syracuseStep 2990621 = 1121483) B1121483
theorem B2368061 : Blo 698317 2368061 := bstep (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) B888023
theorem B5972939 : Blo 698317 5972939 := bstep (se 1 (by rfl) ⟨4479704, by rfl⟩ : syracuseStep 5972939 = 8959409) B8959409
theorem B2237711 : Blo 698317 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B1680841 : Blo 698317 1680841 := bstep (se 2 (by rfl) ⟨630315, by rfl⟩ : syracuseStep 1680841 = 1260631) B1260631
theorem B32253515 : Blo 698317 32253515 := bstep (se 1 (by rfl) ⟨24190136, by rfl⟩ : syracuseStep 32253515 = 48380273) B48380273
theorem B28747637 : Blo 698317 28747637 := bstep (se 5 (by rfl) ⟨1347545, by rfl⟩ : syracuseStep 28747637 = 2695091) B2695091
theorem B2369465 : Blo 698317 2369465 := bstep (se 2 (by rfl) ⟨888549, by rfl⟩ : syracuseStep 2369465 = 1777099) B1777099
theorem B698375 : Blo 698317 698375 := bstep (se 1 (by rfl) ⟨523781, by rfl⟩ : syracuseStep 698375 = 1047563) B1047563
theorem B698383 : Blo 698317 698383 := bstep (se 1 (by rfl) ⟨523787, by rfl⟩ : syracuseStep 698383 = 1047575) B1047575
theorem B698427 : Blo 698317 698427 := bstep (se 1 (by rfl) ⟨523820, by rfl⟩ : syracuseStep 698427 = 1047641) B1047641
theorem B698503 : Blo 698317 698503 := bstep (se 1 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 698503 = 1047755) B1047755
theorem B698511 : Blo 698317 698511 := bstep (se 1 (by rfl) ⟨523883, by rfl⟩ : syracuseStep 698511 = 1047767) B1047767
theorem B698555 : Blo 698317 698555 := bstep (se 1 (by rfl) ⟨523916, by rfl⟩ : syracuseStep 698555 = 1047833) B1047833
theorem B698631 : Blo 698317 698631 := bstep (se 1 (by rfl) ⟨523973, by rfl⟩ : syracuseStep 698631 = 1047947) B1047947
theorem B698639 : Blo 698317 698639 := bstep (se 1 (by rfl) ⟨523979, by rfl⟩ : syracuseStep 698639 = 1047959) B1047959
theorem B3844367 : Blo 698317 3844367 := bstep (se 1 (by rfl) ⟨2883275, by rfl⟩ : syracuseStep 3844367 = 5766551) B5766551
theorem B698683 : Blo 698317 698683 := bstep (se 1 (by rfl) ⟨524012, by rfl⟩ : syracuseStep 698683 = 1048025) B1048025
theorem B698759 : Blo 698317 698759 := bstep (se 1 (by rfl) ⟨524069, by rfl⟩ : syracuseStep 698759 = 1048139) B1048139
theorem B698767 : Blo 698317 698767 := bstep (se 1 (by rfl) ⟨524075, by rfl⟩ : syracuseStep 698767 = 1048151) B1048151
theorem B698811 : Blo 698317 698811 := bstep (se 1 (by rfl) ⟨524108, by rfl⟩ : syracuseStep 698811 = 1048217) B1048217
theorem B698887 : Blo 698317 698887 := bstep (se 1 (by rfl) ⟨524165, by rfl⟩ : syracuseStep 698887 = 1048331) B1048331
theorem B2370059 : Blo 698317 2370059 := bstep (se 1 (by rfl) ⟨1777544, by rfl⟩ : syracuseStep 2370059 = 3555089) B3555089
theorem B698895 : Blo 698317 698895 := bstep (se 1 (by rfl) ⟨524171, by rfl⟩ : syracuseStep 698895 = 1048343) B1048343
theorem B698939 : Blo 698317 698939 := bstep (se 1 (by rfl) ⟨524204, by rfl⟩ : syracuseStep 698939 = 1048409) B1048409
theorem B1518139 : Blo 698317 1518139 := bstep (se 1 (by rfl) ⟨1138604, by rfl⟩ : syracuseStep 1518139 = 2277209) B2277209
theorem B2370167 : Blo 698317 2370167 := bstep (se 1 (by rfl) ⟨1777625, by rfl⟩ : syracuseStep 2370167 = 3555251) B3555251
theorem B699015 : Blo 698317 699015 := bstep (se 1 (by rfl) ⟨524261, by rfl⟩ : syracuseStep 699015 = 1048523) B1048523
theorem B699023 : Blo 698317 699023 := bstep (se 1 (by rfl) ⟨524267, by rfl⟩ : syracuseStep 699023 = 1048535) B1048535
theorem B699067 : Blo 698317 699067 := bstep (se 1 (by rfl) ⟨524300, by rfl⟩ : syracuseStep 699067 = 1048601) B1048601
theorem B699143 : Blo 698317 699143 := bstep (se 1 (by rfl) ⟨524357, by rfl⟩ : syracuseStep 699143 = 1048715) B1048715
theorem B699151 : Blo 698317 699151 := bstep (se 1 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 699151 = 1048727) B1048727
theorem B699195 : Blo 698317 699195 := bstep (se 1 (by rfl) ⟨524396, by rfl⟩ : syracuseStep 699195 = 1048793) B1048793
theorem B3550067 : Blo 698317 3550067 := bstep (se 1 (by rfl) ⟨2662550, by rfl⟩ : syracuseStep 3550067 = 5325101) B5325101
theorem B2665331 : Blo 698317 2665331 := bstep (se 1 (by rfl) ⟨1998998, by rfl⟩ : syracuseStep 2665331 = 3997997) B3997997
theorem B699271 : Blo 698317 699271 := bstep (se 1 (by rfl) ⟨524453, by rfl⟩ : syracuseStep 699271 = 1048907) B1048907
theorem B699279 : Blo 698317 699279 := bstep (se 1 (by rfl) ⟨524459, by rfl⟩ : syracuseStep 699279 = 1048919) B1048919
theorem B3779513 : Blo 698317 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B699323 : Blo 698317 699323 := bstep (se 1 (by rfl) ⟨524492, by rfl⟩ : syracuseStep 699323 = 1048985) B1048985
theorem B699399 : Blo 698317 699399 := bstep (se 1 (by rfl) ⟨524549, by rfl⟩ : syracuseStep 699399 = 1049099) B1049099
theorem B699407 : Blo 698317 699407 := bstep (se 1 (by rfl) ⟨524555, by rfl⟩ : syracuseStep 699407 = 1049111) B1049111
theorem B699451 : Blo 698317 699451 := bstep (se 1 (by rfl) ⟨524588, by rfl⟩ : syracuseStep 699451 = 1049177) B1049177
theorem B2993219 : Blo 698317 2993219 := bstep (se 1 (by rfl) ⟨2244914, by rfl⟩ : syracuseStep 2993219 = 4489829) B4489829
theorem B699527 : Blo 698317 699527 := bstep (se 1 (by rfl) ⟨524645, by rfl⟩ : syracuseStep 699527 = 1049291) B1049291
theorem B994447 : Blo 698317 994447 := bstep (se 1 (by rfl) ⟨745835, by rfl⟩ : syracuseStep 994447 = 1491671) B1491671
theorem B699535 : Blo 698317 699535 := bstep (se 1 (by rfl) ⟨524651, by rfl⟩ : syracuseStep 699535 = 1049303) B1049303
theorem B699579 : Blo 698317 699579 := bstep (se 1 (by rfl) ⟨524684, by rfl⟩ : syracuseStep 699579 = 1049369) B1049369
theorem B699655 : Blo 698317 699655 := bstep (se 1 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 699655 = 1049483) B1049483
theorem B699663 : Blo 698317 699663 := bstep (se 1 (by rfl) ⟨524747, by rfl⟩ : syracuseStep 699663 = 1049495) B1049495
theorem B699707 : Blo 698317 699707 := bstep (se 1 (by rfl) ⟨524780, by rfl⟩ : syracuseStep 699707 = 1049561) B1049561
theorem B3550553 : Blo 698317 3550553 := bstep (se 2 (by rfl) ⟨1331457, by rfl⟩ : syracuseStep 3550553 = 2662915) B2662915
theorem B699783 : Blo 698317 699783 := bstep (se 1 (by rfl) ⟨524837, by rfl⟩ : syracuseStep 699783 = 1049675) B1049675
theorem B699791 : Blo 698317 699791 := bstep (se 1 (by rfl) ⟨524843, by rfl⟩ : syracuseStep 699791 = 1049687) B1049687
theorem B5680529 : Blo 698317 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B2993593 : Blo 698317 2993593 := bstep (se 2 (by rfl) ⟨1122597, by rfl⟩ : syracuseStep 2993593 = 2245195) B2245195
theorem B699835 : Blo 698317 699835 := bstep (se 1 (by rfl) ⟨524876, by rfl⟩ : syracuseStep 699835 = 1049753) B1049753
theorem B699911 : Blo 698317 699911 := bstep (se 1 (by rfl) ⟨524933, by rfl⟩ : syracuseStep 699911 = 1049867) B1049867
theorem B699919 : Blo 698317 699919 := bstep (se 1 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 699919 = 1049879) B1049879
theorem B699963 : Blo 698317 699963 := bstep (se 1 (by rfl) ⟨524972, by rfl⟩ : syracuseStep 699963 = 1049945) B1049945
theorem B700039 : Blo 698317 700039 := bstep (se 1 (by rfl) ⟨525029, by rfl⟩ : syracuseStep 700039 = 1050059) B1050059
theorem B700047 : Blo 698317 700047 := bstep (se 1 (by rfl) ⟨525035, by rfl⟩ : syracuseStep 700047 = 1050071) B1050071
theorem B700091 : Blo 698317 700091 := bstep (se 1 (by rfl) ⟨525068, by rfl⟩ : syracuseStep 700091 = 1050137) B1050137
theorem B995017 : Blo 698317 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B700167 : Blo 698317 700167 := bstep (se 1 (by rfl) ⟨525125, by rfl⟩ : syracuseStep 700167 = 1050251) B1050251
theorem B700175 : Blo 698317 700175 := bstep (se 1 (by rfl) ⟨525131, by rfl⟩ : syracuseStep 700175 = 1050263) B1050263
theorem B7286543 : Blo 698317 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B2993935 : Blo 698317 2993935 := bstep (se 1 (by rfl) ⟨2245451, by rfl⟩ : syracuseStep 2993935 = 4490903) B4490903
theorem B700219 : Blo 698317 700219 := bstep (se 1 (by rfl) ⟨525164, by rfl⟩ : syracuseStep 700219 = 1050329) B1050329
theorem B700295 : Blo 698317 700295 := bstep (se 1 (by rfl) ⟨525221, by rfl⟩ : syracuseStep 700295 = 1050443) B1050443
theorem B700303 : Blo 698317 700303 := bstep (se 1 (by rfl) ⟨525227, by rfl⟩ : syracuseStep 700303 = 1050455) B1050455
theorem B700347 : Blo 698317 700347 := bstep (se 1 (by rfl) ⟨525260, by rfl⟩ : syracuseStep 700347 = 1050521) B1050521
theorem B34090955 : Blo 698317 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B700423 : Blo 698317 700423 := bstep (se 1 (by rfl) ⟨525317, by rfl⟩ : syracuseStep 700423 = 1050635) B1050635
theorem B700431 : Blo 698317 700431 := bstep (se 1 (by rfl) ⟨525323, by rfl⟩ : syracuseStep 700431 = 1050647) B1050647
theorem B5320727 : Blo 698317 5320727 := bstep (se 1 (by rfl) ⟨3990545, by rfl⟩ : syracuseStep 5320727 = 7981091) B7981091
theorem B700475 : Blo 698317 700475 := bstep (se 1 (by rfl) ⟨525356, by rfl⟩ : syracuseStep 700475 = 1050713) B1050713
theorem B700551 : Blo 698317 700551 := bstep (se 1 (by rfl) ⟨525413, by rfl⟩ : syracuseStep 700551 = 1050827) B1050827
theorem B700559 : Blo 698317 700559 := bstep (se 1 (by rfl) ⟨525419, by rfl⟩ : syracuseStep 700559 = 1050839) B1050839
theorem B700603 : Blo 698317 700603 := bstep (se 1 (by rfl) ⟨525452, by rfl⟩ : syracuseStep 700603 = 1050905) B1050905
theorem B700679 : Blo 698317 700679 := bstep (se 1 (by rfl) ⟨525509, by rfl⟩ : syracuseStep 700679 = 1051019) B1051019
theorem B700687 : Blo 698317 700687 := bstep (se 1 (by rfl) ⟨525515, by rfl⟩ : syracuseStep 700687 = 1051031) B1051031
theorem B700731 : Blo 698317 700731 := bstep (se 1 (by rfl) ⟨525548, by rfl⟩ : syracuseStep 700731 = 1051097) B1051097
theorem B700807 : Blo 698317 700807 := bstep (se 1 (by rfl) ⟨525605, by rfl⟩ : syracuseStep 700807 = 1051211) B1051211
theorem B700815 : Blo 698317 700815 := bstep (se 1 (by rfl) ⟨525611, by rfl⟩ : syracuseStep 700815 = 1051223) B1051223
theorem B700859 : Blo 698317 700859 := bstep (se 1 (by rfl) ⟨525644, by rfl⟩ : syracuseStep 700859 = 1051289) B1051289
theorem B700935 : Blo 698317 700935 := bstep (se 1 (by rfl) ⟨525701, by rfl⟩ : syracuseStep 700935 = 1051403) B1051403
theorem B700943 : Blo 698317 700943 := bstep (se 1 (by rfl) ⟨525707, by rfl⟩ : syracuseStep 700943 = 1051415) B1051415
theorem B700987 : Blo 698317 700987 := bstep (se 1 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 700987 = 1051481) B1051481
theorem B3191357 : Blo 698317 3191357 := bstep (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) B1196759
theorem B701063 : Blo 698317 701063 := bstep (se 1 (by rfl) ⟨525797, by rfl⟩ : syracuseStep 701063 = 1051595) B1051595
theorem B701071 : Blo 698317 701071 := bstep (se 1 (by rfl) ⟨525803, by rfl⟩ : syracuseStep 701071 = 1051607) B1051607
theorem B701115 : Blo 698317 701115 := bstep (se 1 (by rfl) ⟨525836, by rfl⟩ : syracuseStep 701115 = 1051673) B1051673
theorem B701191 : Blo 698317 701191 := bstep (se 1 (by rfl) ⟨525893, by rfl⟩ : syracuseStep 701191 = 1051787) B1051787
theorem B701199 : Blo 698317 701199 := bstep (se 1 (by rfl) ⟨525899, by rfl⟩ : syracuseStep 701199 = 1051799) B1051799
theorem B3978017 : Blo 698317 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B701243 : Blo 698317 701243 := bstep (se 1 (by rfl) ⟨525932, by rfl⟩ : syracuseStep 701243 = 1051865) B1051865
theorem B701319 : Blo 698317 701319 := bstep (se 1 (by rfl) ⟨525989, by rfl⟩ : syracuseStep 701319 = 1051979) B1051979
theorem B701327 : Blo 698317 701327 := bstep (se 1 (by rfl) ⟨525995, by rfl⟩ : syracuseStep 701327 = 1051991) B1051991
theorem B701371 : Blo 698317 701371 := bstep (se 1 (by rfl) ⟨526028, by rfl⟩ : syracuseStep 701371 = 1052057) B1052057
theorem B701447 : Blo 698317 701447 := bstep (se 1 (by rfl) ⟨526085, by rfl⟩ : syracuseStep 701447 = 1052171) B1052171
theorem B701455 : Blo 698317 701455 := bstep (se 1 (by rfl) ⟨526091, by rfl⟩ : syracuseStep 701455 = 1052183) B1052183
theorem B701499 : Blo 698317 701499 := bstep (se 1 (by rfl) ⟨526124, by rfl⟩ : syracuseStep 701499 = 1052249) B1052249
theorem B701575 : Blo 698317 701575 := bstep (se 1 (by rfl) ⟨526181, by rfl⟩ : syracuseStep 701575 = 1052363) B1052363
theorem B701583 : Blo 698317 701583 := bstep (se 1 (by rfl) ⟨526187, by rfl⟩ : syracuseStep 701583 = 1052375) B1052375
theorem B1848473 : Blo 698317 1848473 := bstep (se 2 (by rfl) ⟨693177, by rfl⟩ : syracuseStep 1848473 = 1386355) B1386355
theorem B701627 : Blo 698317 701627 := bstep (se 1 (by rfl) ⟨526220, by rfl⟩ : syracuseStep 701627 = 1052441) B1052441
theorem B701703 : Blo 698317 701703 := bstep (se 1 (by rfl) ⟨526277, by rfl⟩ : syracuseStep 701703 = 1052555) B1052555
theorem B800015 : Blo 698317 800015 := bstep (se 1 (by rfl) ⟨600011, by rfl⟩ : syracuseStep 800015 = 1200023) B1200023
theorem B701711 : Blo 698317 701711 := bstep (se 1 (by rfl) ⟨526283, by rfl⟩ : syracuseStep 701711 = 1052567) B1052567
theorem B3355937 : Blo 698317 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B3847475 : Blo 698317 3847475 := bstep (se 1 (by rfl) ⟨2885606, by rfl⟩ : syracuseStep 3847475 = 5771213) B5771213
theorem B701755 : Blo 698317 701755 := bstep (se 1 (by rfl) ⟨526316, by rfl⟩ : syracuseStep 701755 = 1052633) B1052633
theorem B701831 : Blo 698317 701831 := bstep (se 1 (by rfl) ⟨526373, by rfl⟩ : syracuseStep 701831 = 1052747) B1052747
theorem B701839 : Blo 698317 701839 := bstep (se 1 (by rfl) ⟨526379, by rfl⟩ : syracuseStep 701839 = 1052759) B1052759
theorem B3552659 : Blo 698317 3552659 := bstep (se 1 (by rfl) ⟨2664494, by rfl⟩ : syracuseStep 3552659 = 5328989) B5328989
theorem B6403475 : Blo 698317 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B701883 : Blo 698317 701883 := bstep (se 1 (by rfl) ⟨526412, by rfl⟩ : syracuseStep 701883 = 1052825) B1052825
theorem B701959 : Blo 698317 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B701967 : Blo 698317 701967 := bstep (se 1 (by rfl) ⟨526475, by rfl⟩ : syracuseStep 701967 = 1052951) B1052951
theorem B702011 : Blo 698317 702011 := bstep (se 1 (by rfl) ⟨526508, by rfl⟩ : syracuseStep 702011 = 1053017) B1053017
theorem B702087 : Blo 698317 702087 := bstep (se 1 (by rfl) ⟨526565, by rfl⟩ : syracuseStep 702087 = 1053131) B1053131
theorem B702095 : Blo 698317 702095 := bstep (se 1 (by rfl) ⟨526571, by rfl⟩ : syracuseStep 702095 = 1053143) B1053143
theorem B1619603 : Blo 698317 1619603 := bstep (se 1 (by rfl) ⟨1214702, by rfl⟩ : syracuseStep 1619603 = 2429405) B2429405
theorem B702139 : Blo 698317 702139 := bstep (se 1 (by rfl) ⟨526604, by rfl⟩ : syracuseStep 702139 = 1053209) B1053209
theorem B3847873 : Blo 698317 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B702215 : Blo 698317 702215 := bstep (se 1 (by rfl) ⟨526661, by rfl⟩ : syracuseStep 702215 = 1053323) B1053323
theorem B702223 : Blo 698317 702223 := bstep (se 1 (by rfl) ⟨526667, by rfl⟩ : syracuseStep 702223 = 1053335) B1053335
theorem B1685281 : Blo 698317 1685281 := bstep (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) B1263961
theorem B702267 : Blo 698317 702267 := bstep (se 1 (by rfl) ⟨526700, by rfl⟩ : syracuseStep 702267 = 1053401) B1053401
theorem B1914881 : Blo 698317 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B1554491 : Blo 698317 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B2996311 : Blo 698317 2996311 := bstep (se 1 (by rfl) ⟨2247233, by rfl⟩ : syracuseStep 2996311 = 4494467) B4494467
theorem B1685819 : Blo 698317 1685819 := bstep (se 1 (by rfl) ⟨1264364, by rfl⟩ : syracuseStep 1685819 = 2528729) B2528729
theorem B997705 : Blo 698317 997705 := bstep (se 2 (by rfl) ⟨374139, by rfl⟩ : syracuseStep 997705 = 748279) B748279
theorem B1063543 : Blo 698317 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B1817387 : Blo 698317 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B23313419 : Blo 698317 23313419 := bstep (se 1 (by rfl) ⟨17485064, by rfl⟩ : syracuseStep 23313419 = 34970129) B34970129
theorem B1686587 : Blo 698317 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B3587159 : Blo 698317 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B3030419 : Blo 698317 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B8535581 : Blo 698317 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B1064711 : Blo 698317 1064711 := bstep (se 1 (by rfl) ⟨798533, by rfl⟩ : syracuseStep 1064711 = 1597067) B1597067
theorem B2834311 : Blo 698317 2834311 := bstep (se 1 (by rfl) ⟨2125733, by rfl⟩ : syracuseStep 2834311 = 4251467) B4251467
theorem B8503319 : Blo 698317 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B3784877 : Blo 698317 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B1327403 : Blo 698317 1327403 := bstep (se 1 (by rfl) ⟨995552, by rfl⟩ : syracuseStep 1327403 = 1991105) B1991105
theorem B3359027 : Blo 698317 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B5980625 : Blo 698317 5980625 := bstep (se 2 (by rfl) ⟨2242734, by rfl⟩ : syracuseStep 5980625 = 4485469) B4485469
theorem B1328329 : Blo 698317 1328329 := bstep (se 2 (by rfl) ⟨498123, by rfl⟩ : syracuseStep 1328329 = 996247) B996247
theorem B3982891 : Blo 698317 3982891 := bstep (se 1 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 3982891 = 5974337) B5974337
theorem B2049907 : Blo 698317 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B1329043 : Blo 698317 1329043 := bstep (se 1 (by rfl) ⟨996782, by rfl⟩ : syracuseStep 1329043 = 1993565) B1993565
theorem B3360797 : Blo 698317 3360797 := bstep (se 3 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 3360797 = 1260299) B1260299
theorem B4475195 : Blo 698317 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B4475321 : Blo 698317 4475321 := bstep (se 2 (by rfl) ⟨1678245, by rfl⟩ : syracuseStep 4475321 = 3356491) B3356491
theorem B2837035 : Blo 698317 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B2247439 : Blo 698317 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B3361625 : Blo 698317 3361625 := bstep (se 2 (by rfl) ⟨1260609, by rfl⟩ : syracuseStep 3361625 = 2521219) B2521219
theorem B2018249 : Blo 698317 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B1330121 : Blo 698317 1330121 := bstep (se 2 (by rfl) ⟨498795, by rfl⟩ : syracuseStep 1330121 = 997591) B997591
theorem B3984349 : Blo 698317 3984349 := bstep (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) B1494131
theorem B1494217 : Blo 698317 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B5328503 : Blo 698317 5328503 := bstep (se 1 (by rfl) ⟨3996377, by rfl⟩ : syracuseStep 5328503 = 7992755) B7992755
theorem B1265287 : Blo 698317 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B1494713 : Blo 698317 1494713 := bstep (se 2 (by rfl) ⟨560517, by rfl⟩ : syracuseStep 1494713 = 1121035) B1121035
theorem B1330987 : Blo 698317 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B17977139 : Blo 698317 17977139 := bstep (se 1 (by rfl) ⟨13482854, by rfl⟩ : syracuseStep 17977139 = 26965709) B26965709
theorem B1331063 : Blo 698317 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B1888697 : Blo 698317 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B3363257 : Blo 698317 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B5329475 : Blo 698317 5329475 := bstep (se 1 (by rfl) ⟨3997106, by rfl⟩ : syracuseStep 5329475 = 7994213) B7994213
theorem B3363565 : Blo 698317 3363565 := bstep (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) B1261337
theorem B6738967 : Blo 698317 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B30626885 : Blo 698317 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B1496353 : Blo 698317 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B1889671 : Blo 698317 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B5985683 : Blo 698317 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B3200573 : Blo 698317 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B8509157 : Blo 698317 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B841487 : Blo 698317 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B1333007 : Blo 698317 1333007 := bstep (se 1 (by rfl) ⟨999755, by rfl⟩ : syracuseStep 1333007 = 1999511) B1999511
theorem B1496951 : Blo 698317 1496951 := bstep (se 1 (by rfl) ⟨1122713, by rfl⟩ : syracuseStep 1496951 = 2245427) B2245427
theorem B1136825 : Blo 698317 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B1137097 : Blo 698317 1137097 := bstep (se 2 (by rfl) ⟨426411, by rfl⟩ : syracuseStep 1137097 = 852823) B852823
theorem B1989305 : Blo 698317 1989305 := bstep (se 2 (by rfl) ⟨745989, by rfl⟩ : syracuseStep 1989305 = 1491979) B1491979
theorem B1989647 : Blo 698317 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B3988541 : Blo 698317 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B7691537 : Blo 698317 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B3989249 : Blo 698317 3989249 := bstep (se 2 (by rfl) ⟨1495968, by rfl⟩ : syracuseStep 3989249 = 2991937) B2991937
theorem B1990433 : Blo 698317 1990433 := bstep (se 2 (by rfl) ⟨746412, by rfl⟩ : syracuseStep 1990433 = 1492825) B1492825
theorem B3792919 : Blo 698317 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B1794163 : Blo 698317 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B4251905 : Blo 698317 4251905 := bstep (se 2 (by rfl) ⟨1594464, by rfl⟩ : syracuseStep 4251905 = 3188929) B3188929
theorem B2154763 : Blo 698317 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B36397457 : Blo 698317 36397457 := bstep (se 2 (by rfl) ⟨13649046, by rfl⟩ : syracuseStep 36397457 = 27298093) B27298093
theorem B1794575 : Blo 698317 1794575 := bstep (se 1 (by rfl) ⟨1345931, by rfl⟩ : syracuseStep 1794575 = 2691863) B2691863
theorem B4252247 : Blo 698317 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B8774245 : Blo 698317 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B2843425 : Blo 698317 2843425 := bstep (se 2 (by rfl) ⟨1066284, by rfl⟩ : syracuseStep 2843425 = 2132569) B2132569
theorem B43082533 : Blo 698317 43082533 := bstep (se 4 (by rfl) ⟨4038987, by rfl⟩ : syracuseStep 43082533 = 8077975) B8077975
theorem B1991947 : Blo 698317 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B746767 : Blo 698317 746767 := bstep (se 1 (by rfl) ⟨560075, by rfl⟩ : syracuseStep 746767 = 1120151) B1120151
theorem B1992221 : Blo 698317 1992221 := bstep (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) B747083
theorem B1992563 : Blo 698317 1992563 := bstep (se 1 (by rfl) ⟨1494422, by rfl⟩ : syracuseStep 1992563 = 2988845) B2988845
theorem B747527 : Blo 698317 747527 := bstep (se 1 (by rfl) ⟨560645, by rfl⟩ : syracuseStep 747527 = 1121291) B1121291
theorem B5040215 : Blo 698317 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B3991639 : Blo 698317 3991639 := bstep (se 1 (by rfl) ⟨2993729, by rfl⟩ : syracuseStep 3991639 = 5987459) B5987459
theorem B2123911 : Blo 698317 2123911 := bstep (se 1 (by rfl) ⟨1592933, by rfl⟩ : syracuseStep 2123911 = 3185867) B3185867
theorem B2517571 : Blo 698317 2517571 := bstep (se 1 (by rfl) ⟨1888178, by rfl⟩ : syracuseStep 2517571 = 3776357) B3776357
theorem B1993531 : Blo 698317 1993531 := bstep (se 1 (by rfl) ⟨1495148, by rfl⟩ : syracuseStep 1993531 = 2990297) B2990297
theorem B2517875 : Blo 698317 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B3796205 : Blo 698317 3796205 := bstep (se 3 (by rfl) ⟨711788, by rfl⟩ : syracuseStep 3796205 = 1423577) B1423577
theorem B1895681 : Blo 698317 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B10087811 : Blo 698317 10087811 := bstep (se 1 (by rfl) ⟨7565858, by rfl⟩ : syracuseStep 10087811 = 15131717) B15131717
theorem B945851 : Blo 698317 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B3796769 : Blo 698317 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B1994681 : Blo 698317 1994681 := bstep (se 2 (by rfl) ⟨748005, by rfl⟩ : syracuseStep 1994681 = 1496011) B1496011
theorem B3993623 : Blo 698317 3993623 := bstep (se 1 (by rfl) ⟨2995217, by rfl⟩ : syracuseStep 3993623 = 5990435) B5990435
theorem B1995023 : Blo 698317 1995023 := bstep (se 1 (by rfl) ⟨1496267, by rfl⟩ : syracuseStep 1995023 = 2992535) B2992535
theorem B1798433 : Blo 698317 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B1896851 : Blo 698317 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B3535325 : Blo 698317 3535325 := bstep (se 3 (by rfl) ⟨662873, by rfl⟩ : syracuseStep 3535325 = 1325747) B1325747
theorem B3535649 : Blo 698317 3535649 := bstep (se 2 (by rfl) ⟨1325868, by rfl⟩ : syracuseStep 3535649 = 2651737) B2651737
theorem B45413297 : Blo 698317 45413297 := bstep (se 2 (by rfl) ⟨17029986, by rfl⟩ : syracuseStep 45413297 = 34059973) B34059973
theorem B1995911 : Blo 698317 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B947387 : Blo 698317 947387 := bstep (se 1 (by rfl) ⟨710540, by rfl⟩ : syracuseStep 947387 = 1421081) B1421081
theorem B1897757 : Blo 698317 1897757 := bstep (se 3 (by rfl) ⟨355829, by rfl⟩ : syracuseStep 1897757 = 711659) B711659
theorem B8516897 : Blo 698317 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1996093 : Blo 698317 1996093 := bstep (se 3 (by rfl) ⟨374267, by rfl⟩ : syracuseStep 1996093 = 748535) B748535
theorem B1996321 : Blo 698317 1996321 := bstep (se 2 (by rfl) ⟨748620, by rfl⟩ : syracuseStep 1996321 = 1497241) B1497241
theorem B1799827 : Blo 698317 1799827 := bstep (se 1 (by rfl) ⟨1349870, by rfl⟩ : syracuseStep 1799827 = 2699741) B2699741
theorem B2356937 : Blo 698317 2356937 := bstep (se 2 (by rfl) ⟨883851, by rfl⟩ : syracuseStep 2356937 = 1767703) B1767703
theorem B3536621 : Blo 698317 3536621 := bstep (se 3 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 3536621 = 1326233) B1326233
theorem B13498163 : Blo 698317 13498163 := bstep (se 1 (by rfl) ⟨10123622, by rfl⟩ : syracuseStep 13498163 = 20247245) B20247245
theorem B1996663 : Blo 698317 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B3372947 : Blo 698317 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B16152817 : Blo 698317 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1767815 : Blo 698317 1767815 := bstep (se 1 (by rfl) ⟨1325861, by rfl⟩ : syracuseStep 1767815 = 2651723) B2651723
theorem B2357639 : Blo 698317 2357639 := bstep (se 1 (by rfl) ⟨1768229, by rfl⟩ : syracuseStep 2357639 = 3536459) B3536459
theorem B1571219 : Blo 698317 1571219 := bstep (se 1 (by rfl) ⟨1178414, by rfl⟩ : syracuseStep 1571219 = 2356829) B2356829
theorem B14383507 : Blo 698317 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B1767865 : Blo 698317 1767865 := bstep (se 2 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 1767865 = 1325899) B1325899
theorem B1571273 : Blo 698317 1571273 := bstep (se 2 (by rfl) ⟨589227, by rfl⟩ : syracuseStep 1571273 = 1178455) B1178455
theorem B3537431 : Blo 698317 3537431 := bstep (se 1 (by rfl) ⟨2653073, by rfl⟩ : syracuseStep 3537431 = 5306147) B5306147
theorem B2358017 : Blo 698317 2358017 := bstep (se 2 (by rfl) ⟨884256, by rfl⟩ : syracuseStep 2358017 = 1768513) B1768513
theorem B1997597 : Blo 698317 1997597 := bstep (se 3 (by rfl) ⟨374549, by rfl⟩ : syracuseStep 1997597 = 749099) B749099
theorem B6716209 : Blo 698317 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B1047497 : Blo 698317 1047497 := bstep (se 2 (by rfl) ⟨392811, by rfl⟩ : syracuseStep 1047497 = 785623) B785623
theorem B2653195 : Blo 698317 2653195 := bstep (se 1 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 2653195 = 3979793) B3979793
theorem B1768463 : Blo 698317 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B1047611 : Blo 698317 1047611 := bstep (se 1 (by rfl) ⟨785708, by rfl⟩ : syracuseStep 1047611 = 1571417) B1571417
theorem B1997939 : Blo 698317 1997939 := bstep (se 1 (by rfl) ⟨1498454, by rfl⟩ : syracuseStep 1997939 = 2996909) B2996909
theorem B1047671 : Blo 698317 1047671 := bstep (se 1 (by rfl) ⟨785753, by rfl⟩ : syracuseStep 1047671 = 1571507) B1571507
theorem B1178759 : Blo 698317 1178759 := bstep (se 1 (by rfl) ⟨884069, by rfl⟩ : syracuseStep 1178759 = 1768139) B1768139
theorem B1571975 : Blo 698317 1571975 := bstep (se 1 (by rfl) ⟨1178981, by rfl⟩ : syracuseStep 1571975 = 2357963) B2357963
theorem B1047695 : Blo 698317 1047695 := bstep (se 1 (by rfl) ⟨785771, by rfl⟩ : syracuseStep 1047695 = 1571543) B1571543
theorem B1047737 : Blo 698317 1047737 := bstep (se 2 (by rfl) ⟨392901, by rfl⟩ : syracuseStep 1047737 = 785803) B785803
theorem B1047815 : Blo 698317 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B1047851 : Blo 698317 1047851 := bstep (se 1 (by rfl) ⟨785888, by rfl⟩ : syracuseStep 1047851 = 1571777) B1571777
theorem B1572155 : Blo 698317 1572155 := bstep (se 1 (by rfl) ⟨1179116, by rfl⟩ : syracuseStep 1572155 = 2358233) B2358233
theorem B2653499 : Blo 698317 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B1047881 : Blo 698317 1047881 := bstep (se 2 (by rfl) ⟨392955, by rfl⟩ : syracuseStep 1047881 = 785911) B785911
theorem B1572281 : Blo 698317 1572281 := bstep (se 2 (by rfl) ⟨589605, by rfl⟩ : syracuseStep 1572281 = 1179211) B1179211
theorem B1047995 : Blo 698317 1047995 := bstep (se 1 (by rfl) ⟨785996, by rfl⟩ : syracuseStep 1047995 = 1571993) B1571993
theorem B11369933 : Blo 698317 11369933 := bstep (se 3 (by rfl) ⟨2131862, by rfl⟩ : syracuseStep 11369933 = 4263725) B4263725
theorem B1048055 : Blo 698317 1048055 := bstep (se 1 (by rfl) ⟨786041, by rfl⟩ : syracuseStep 1048055 = 1572083) B1572083
theorem B1048079 : Blo 698317 1048079 := bstep (se 1 (by rfl) ⟨786059, by rfl⟩ : syracuseStep 1048079 = 1572119) B1572119
theorem B2358827 : Blo 698317 2358827 := bstep (se 1 (by rfl) ⟨1769120, by rfl⟩ : syracuseStep 2358827 = 3538241) B3538241
theorem B1048121 : Blo 698317 1048121 := bstep (se 2 (by rfl) ⟨393045, by rfl⟩ : syracuseStep 1048121 = 786091) B786091
theorem B1998395 : Blo 698317 1998395 := bstep (se 1 (by rfl) ⟨1498796, by rfl⟩ : syracuseStep 1998395 = 2997593) B2997593
theorem B786055 : Blo 698317 786055 := bstep (se 1 (by rfl) ⟨589541, by rfl⟩ : syracuseStep 786055 = 1179083) B1179083
theorem B1048199 : Blo 698317 1048199 := bstep (se 1 (by rfl) ⟨786149, by rfl⟩ : syracuseStep 1048199 = 1572299) B1572299
theorem B1048235 : Blo 698317 1048235 := bstep (se 1 (by rfl) ⟨786176, by rfl⟩ : syracuseStep 1048235 = 1572353) B1572353
theorem B1048265 : Blo 698317 1048265 := bstep (se 2 (by rfl) ⟨393099, by rfl⟩ : syracuseStep 1048265 = 786199) B786199
theorem B1769161 : Blo 698317 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B1179407 : Blo 698317 1179407 := bstep (se 1 (by rfl) ⟨884555, by rfl⟩ : syracuseStep 1179407 = 1769111) B1769111
theorem B1572623 : Blo 698317 1572623 := bstep (se 1 (by rfl) ⟨1179467, by rfl⟩ : syracuseStep 1572623 = 2358935) B2358935
theorem B1572641 : Blo 698317 1572641 := bstep (se 2 (by rfl) ⟨589740, by rfl⟩ : syracuseStep 1572641 = 1179481) B1179481
theorem B2653985 : Blo 698317 2653985 := bstep (se 2 (by rfl) ⟨995244, by rfl⟩ : syracuseStep 2653985 = 1990489) B1990489
theorem B786235 : Blo 698317 786235 := bstep (se 1 (by rfl) ⟨589676, by rfl⟩ : syracuseStep 786235 = 1179353) B1179353
theorem B1048379 : Blo 698317 1048379 := bstep (se 1 (by rfl) ⟨786284, by rfl⟩ : syracuseStep 1048379 = 1572569) B1572569
theorem B2129723 : Blo 698317 2129723 := bstep (se 1 (by rfl) ⟨1597292, by rfl⟩ : syracuseStep 2129723 = 3194585) B3194585
theorem B1769303 : Blo 698317 1769303 := bstep (se 1 (by rfl) ⟨1326977, by rfl⟩ : syracuseStep 1769303 = 2653955) B2653955
theorem B1048439 : Blo 698317 1048439 := bstep (se 1 (by rfl) ⟨786329, by rfl⟩ : syracuseStep 1048439 = 1572659) B1572659
theorem B1048463 : Blo 698317 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B1048505 : Blo 698317 1048505 := bstep (se 2 (by rfl) ⟨393189, by rfl⟩ : syracuseStep 1048505 = 786379) B786379
theorem B5668879 : Blo 698317 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B1048655 : Blo 698317 1048655 := bstep (se 1 (by rfl) ⟨786491, by rfl⟩ : syracuseStep 1048655 = 1572983) B1572983
theorem B2523251 : Blo 698317 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B2392217 : Blo 698317 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B1048775 : Blo 698317 1048775 := bstep (se 1 (by rfl) ⟨786581, by rfl⟩ : syracuseStep 1048775 = 1573163) B1573163
theorem B884935 : Blo 698317 884935 := bstep (se 1 (by rfl) ⟨663701, by rfl⟩ : syracuseStep 884935 = 1327403) B1327403
theorem B786631 : Blo 698317 786631 := bstep (se 1 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 786631 = 1179947) B1179947
theorem B1048937 : Blo 698317 1048937 := bstep (se 2 (by rfl) ⟨393351, by rfl⟩ : syracuseStep 1048937 = 786703) B786703
theorem B1049015 : Blo 698317 1049015 := bstep (se 1 (by rfl) ⟨786761, by rfl⟩ : syracuseStep 1049015 = 1573523) B1573523
theorem B5046731 : Blo 698317 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B1049051 : Blo 698317 1049051 := bstep (se 1 (by rfl) ⟨786788, by rfl⟩ : syracuseStep 1049051 = 1573577) B1573577
theorem B5767661 : Blo 698317 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B1769971 : Blo 698317 1769971 := bstep (se 1 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 1769971 = 2654957) B2654957
theorem B1573415 : Blo 698317 1573415 := bstep (se 1 (by rfl) ⟨1180061, by rfl⟩ : syracuseStep 1573415 = 2360123) B2360123
theorem B1180217 : Blo 698317 1180217 := bstep (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) B885163
theorem B17990261 : Blo 698317 17990261 := bstep (se 5 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 17990261 = 1686587) B1686587
theorem B5309063 : Blo 698317 5309063 := bstep (se 1 (by rfl) ⟨3981797, by rfl⟩ : syracuseStep 5309063 = 7963595) B7963595
theorem B11698993 : Blo 698317 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B1573739 : Blo 698317 1573739 := bstep (se 1 (by rfl) ⟨1180304, by rfl⟩ : syracuseStep 1573739 = 2360609) B2360609
theorem B1573793 : Blo 698317 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B1049519 : Blo 698317 1049519 := bstep (se 1 (by rfl) ⟨787139, by rfl⟩ : syracuseStep 1049519 = 1574279) B1574279
theorem B1049609 : Blo 698317 1049609 := bstep (se 2 (by rfl) ⟨393603, by rfl⟩ : syracuseStep 1049609 = 787207) B787207
theorem B2360339 : Blo 698317 2360339 := bstep (se 1 (by rfl) ⟨1770254, by rfl⟩ : syracuseStep 2360339 = 3540509) B3540509
theorem B1049639 : Blo 698317 1049639 := bstep (se 1 (by rfl) ⟨787229, by rfl⟩ : syracuseStep 1049639 = 1574459) B1574459
theorem B787495 : Blo 698317 787495 := bstep (se 1 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 787495 = 1181243) B1181243
theorem B57443377 : Blo 698317 57443377 := bstep (se 2 (by rfl) ⟨21541266, by rfl⟩ : syracuseStep 57443377 = 43082533) B43082533
theorem B1049723 : Blo 698317 1049723 := bstep (se 1 (by rfl) ⟨787292, by rfl⟩ : syracuseStep 1049723 = 1574585) B1574585
theorem B1574135 : Blo 698317 1574135 := bstep (se 1 (by rfl) ⟨1180601, by rfl⟩ : syracuseStep 1574135 = 2361203) B2361203
theorem B1180919 : Blo 698317 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B1049849 : Blo 698317 1049849 := bstep (se 2 (by rfl) ⟨393693, by rfl⟩ : syracuseStep 1049849 = 787387) B787387
theorem B2360663 : Blo 698317 2360663 := bstep (se 1 (by rfl) ⟨1770497, by rfl⟩ : syracuseStep 2360663 = 3540995) B3540995
theorem B1049951 : Blo 698317 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B1049963 : Blo 698317 1049963 := bstep (se 1 (by rfl) ⟨787472, by rfl⟩ : syracuseStep 1049963 = 1574945) B1574945
theorem B2983463 : Blo 698317 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B1181263 : Blo 698317 1181263 := bstep (se 1 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 1181263 = 1771895) B1771895
theorem B1050191 : Blo 698317 1050191 := bstep (se 1 (by rfl) ⟨787643, by rfl⟩ : syracuseStep 1050191 = 1575287) B1575287
theorem B1771105 : Blo 698317 1771105 := bstep (se 2 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 1771105 = 1328329) B1328329
theorem B2983547 : Blo 698317 2983547 := bstep (se 1 (by rfl) ⟨2237660, by rfl⟩ : syracuseStep 2983547 = 4475321) B4475321
theorem B2655929 : Blo 698317 2655929 := bstep (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) B1991947
theorem B1050311 : Blo 698317 1050311 := bstep (se 1 (by rfl) ⟨787733, by rfl⟩ : syracuseStep 1050311 = 1575467) B1575467
theorem B1574729 : Blo 698317 1574729 := bstep (se 2 (by rfl) ⟨590523, by rfl⟩ : syracuseStep 1574729 = 1181047) B1181047
theorem B1181513 : Blo 698317 1181513 := bstep (se 2 (by rfl) ⟨443067, by rfl⟩ : syracuseStep 1181513 = 886135) B886135
theorem B1050473 : Blo 698317 1050473 := bstep (se 2 (by rfl) ⟨393927, by rfl⟩ : syracuseStep 1050473 = 787855) B787855
theorem B1050551 : Blo 698317 1050551 := bstep (se 1 (by rfl) ⟨787913, by rfl⟩ : syracuseStep 1050551 = 1575827) B1575827
theorem B1345499 : Blo 698317 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B1050587 : Blo 698317 1050587 := bstep (se 1 (by rfl) ⟨787940, by rfl⟩ : syracuseStep 1050587 = 1575881) B1575881
theorem B5310521 : Blo 698317 5310521 := bstep (se 2 (by rfl) ⟨1991445, by rfl⟩ : syracuseStep 5310521 = 3982891) B3982891
theorem B1181945 : Blo 698317 1181945 := bstep (se 2 (by rfl) ⟨443229, by rfl⟩ : syracuseStep 1181945 = 886459) B886459
theorem B6064517 : Blo 698317 6064517 := bstep (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) B1137097
theorem B2361743 : Blo 698317 2361743 := bstep (se 1 (by rfl) ⟨1771307, by rfl⟩ : syracuseStep 2361743 = 3542615) B3542615
theorem B1182127 : Blo 698317 1182127 := bstep (se 1 (by rfl) ⟨886595, by rfl⟩ : syracuseStep 1182127 = 1773191) B1773191
theorem B1051055 : Blo 698317 1051055 := bstep (se 1 (by rfl) ⟨788291, by rfl⟩ : syracuseStep 1051055 = 1576583) B1576583
theorem B1182215 : Blo 698317 1182215 := bstep (se 1 (by rfl) ⟨886661, by rfl⟩ : syracuseStep 1182215 = 1773323) B1773323
theorem B1051145 : Blo 698317 1051145 := bstep (se 2 (by rfl) ⟨394179, by rfl⟩ : syracuseStep 1051145 = 788359) B788359
theorem B1772057 : Blo 698317 1772057 := bstep (se 2 (by rfl) ⟨664521, by rfl⟩ : syracuseStep 1772057 = 1329043) B1329043
theorem B1051175 : Blo 698317 1051175 := bstep (se 1 (by rfl) ⟨788381, by rfl⟩ : syracuseStep 1051175 = 1576763) B1576763
theorem B887375 : Blo 698317 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B1575521 : Blo 698317 1575521 := bstep (se 2 (by rfl) ⟨590820, by rfl⟩ : syracuseStep 1575521 = 1181641) B1181641
theorem B1051259 : Blo 698317 1051259 := bstep (se 1 (by rfl) ⟨788444, by rfl⟩ : syracuseStep 1051259 = 1576889) B1576889
theorem B789115 : Blo 698317 789115 := bstep (se 1 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 789115 = 1183673) B1183673
theorem B2362067 : Blo 698317 2362067 := bstep (se 1 (by rfl) ⟨1771550, by rfl⟩ : syracuseStep 2362067 = 3543101) B3543101
theorem B1051385 : Blo 698317 1051385 := bstep (se 2 (by rfl) ⟨394269, by rfl⟩ : syracuseStep 1051385 = 788539) B788539
theorem B1182559 : Blo 698317 1182559 := bstep (se 1 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 1182559 = 1773839) B1773839
theorem B1051487 : Blo 698317 1051487 := bstep (se 1 (by rfl) ⟨788615, by rfl⟩ : syracuseStep 1051487 = 1577231) B1577231
theorem B1051499 : Blo 698317 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B1575863 : Blo 698317 1575863 := bstep (se 1 (by rfl) ⟨1181897, by rfl⟩ : syracuseStep 1575863 = 2363795) B2363795
theorem B1182647 : Blo 698317 1182647 := bstep (se 1 (by rfl) ⟨886985, by rfl⟩ : syracuseStep 1182647 = 1773971) B1773971
theorem B1772563 : Blo 698317 1772563 := bstep (se 1 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 1772563 = 2658845) B2658845
theorem B1051727 : Blo 698317 1051727 := bstep (se 1 (by rfl) ⟨788795, by rfl⟩ : syracuseStep 1051727 = 1577591) B1577591
theorem B789583 : Blo 698317 789583 := bstep (se 1 (by rfl) ⟨592187, by rfl⟩ : syracuseStep 789583 = 1184375) B1184375
theorem B2526365 : Blo 698317 2526365 := bstep (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) B947387
theorem B1051847 : Blo 698317 1051847 := bstep (se 1 (by rfl) ⟨788885, by rfl⟩ : syracuseStep 1051847 = 1577771) B1577771
theorem B1052009 : Blo 698317 1052009 := bstep (se 2 (by rfl) ⟨394503, by rfl⟩ : syracuseStep 1052009 = 789007) B789007
theorem B5967229 : Blo 698317 5967229 := bstep (se 3 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 5967229 = 2237711) B2237711
theorem B2133373 : Blo 698317 2133373 := bstep (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) B800015
theorem B20417923 : Blo 698317 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B1052087 : Blo 698317 1052087 := bstep (se 1 (by rfl) ⟨789065, by rfl⟩ : syracuseStep 1052087 = 1578131) B1578131
theorem B1052123 : Blo 698317 1052123 := bstep (se 1 (by rfl) ⟨789092, by rfl⟩ : syracuseStep 1052123 = 1578185) B1578185
theorem B789979 : Blo 698317 789979 := bstep (se 1 (by rfl) ⟨592484, by rfl⟩ : syracuseStep 789979 = 1184969) B1184969
theorem B1576457 : Blo 698317 1576457 := bstep (se 2 (by rfl) ⟨591171, by rfl⟩ : syracuseStep 1576457 = 1182343) B1182343
theorem B1183241 : Blo 698317 1183241 := bstep (se 2 (by rfl) ⟨443715, by rfl⟩ : syracuseStep 1183241 = 887431) B887431
theorem B1183403 : Blo 698317 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B2133715 : Blo 698317 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B3542777 : Blo 698317 3542777 := bstep (se 2 (by rfl) ⟨1328541, by rfl⟩ : syracuseStep 3542777 = 2657083) B2657083
theorem B2658041 : Blo 698317 2658041 := bstep (se 2 (by rfl) ⟨996765, by rfl⟩ : syracuseStep 2658041 = 1993531) B1993531
theorem B5672771 : Blo 698317 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B1576799 : Blo 698317 1576799 := bstep (se 1 (by rfl) ⟨1182599, by rfl⟩ : syracuseStep 1576799 = 2365199) B2365199
theorem B888671 : Blo 698317 888671 := bstep (se 1 (by rfl) ⟨666503, by rfl⟩ : syracuseStep 888671 = 1333007) B1333007
theorem B2363255 : Blo 698317 2363255 := bstep (se 1 (by rfl) ⟨1772441, by rfl⟩ : syracuseStep 2363255 = 3544883) B3544883
theorem B1052591 : Blo 698317 1052591 := bstep (se 1 (by rfl) ⟨789443, by rfl⟩ : syracuseStep 1052591 = 1578887) B1578887
theorem B5312465 : Blo 698317 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B1052681 : Blo 698317 1052681 := bstep (se 2 (by rfl) ⟨394755, by rfl⟩ : syracuseStep 1052681 = 789511) B789511
theorem B1576979 : Blo 698317 1576979 := bstep (se 1 (by rfl) ⟨1182734, by rfl⟩ : syracuseStep 1576979 = 2365469) B2365469
theorem B1052711 : Blo 698317 1052711 := bstep (se 1 (by rfl) ⟨789533, by rfl⟩ : syracuseStep 1052711 = 1579067) B1579067
theorem B1183801 : Blo 698317 1183801 := bstep (se 2 (by rfl) ⟨443925, by rfl⟩ : syracuseStep 1183801 = 887851) B887851
theorem B2363471 : Blo 698317 2363471 := bstep (se 1 (by rfl) ⟨1772603, by rfl⟩ : syracuseStep 2363471 = 3545207) B3545207
theorem B1773647 : Blo 698317 1773647 := bstep (se 1 (by rfl) ⟨1330235, by rfl⟩ : syracuseStep 1773647 = 2660471) B2660471
theorem B757883 : Blo 698317 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B1052795 : Blo 698317 1052795 := bstep (se 1 (by rfl) ⟨789596, by rfl⟩ : syracuseStep 1052795 = 1579193) B1579193
theorem B1183943 : Blo 698317 1183943 := bstep (se 1 (by rfl) ⟨887957, by rfl⟩ : syracuseStep 1183943 = 1775915) B1775915
theorem B1052921 : Blo 698317 1052921 := bstep (se 2 (by rfl) ⟨394845, by rfl⟩ : syracuseStep 1052921 = 789691) B789691
theorem B1053023 : Blo 698317 1053023 := bstep (se 1 (by rfl) ⟨789767, by rfl⟩ : syracuseStep 1053023 = 1579535) B1579535
theorem B1577321 : Blo 698317 1577321 := bstep (se 2 (by rfl) ⟨591495, by rfl⟩ : syracuseStep 1577321 = 1182991) B1182991
theorem B1184105 : Blo 698317 1184105 := bstep (se 2 (by rfl) ⟨444039, by rfl⟩ : syracuseStep 1184105 = 888079) B888079
theorem B1053035 : Blo 698317 1053035 := bstep (se 1 (by rfl) ⟨789776, by rfl⟩ : syracuseStep 1053035 = 1579553) B1579553
theorem B3543425 : Blo 698317 3543425 := bstep (se 2 (by rfl) ⟨1328784, by rfl⟩ : syracuseStep 3543425 = 2657569) B2657569
theorem B2363849 : Blo 698317 2363849 := bstep (se 2 (by rfl) ⟨886443, by rfl⟩ : syracuseStep 2363849 = 1772887) B1772887
theorem B1053263 : Blo 698317 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B1053383 : Blo 698317 1053383 := bstep (se 1 (by rfl) ⟨790037, by rfl⟩ : syracuseStep 1053383 = 1580075) B1580075
theorem B2659027 : Blo 698317 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B2364119 : Blo 698317 2364119 := bstep (se 1 (by rfl) ⟨1773089, by rfl⟩ : syracuseStep 2364119 = 3546179) B3546179
theorem B1774295 : Blo 698317 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B1184503 : Blo 698317 1184503 := bstep (se 1 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 1184503 = 1776755) B1776755
theorem B2364335 : Blo 698317 2364335 := bstep (se 1 (by rfl) ⟨1773251, by rfl⟩ : syracuseStep 2364335 = 3546503) B3546503
theorem B1577915 : Blo 698317 1577915 := bstep (se 1 (by rfl) ⟨1183436, by rfl⟩ : syracuseStep 1577915 = 2366873) B2366873
theorem B1184699 : Blo 698317 1184699 := bstep (se 1 (by rfl) ⟨888524, by rfl⟩ : syracuseStep 1184699 = 1777049) B1777049
theorem B19928065 : Blo 698317 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B1184807 : Blo 698317 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B1774649 : Blo 698317 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B1578041 : Blo 698317 1578041 := bstep (se 2 (by rfl) ⟨591765, by rfl⟩ : syracuseStep 1578041 = 1183531) B1183531
theorem B3544235 : Blo 698317 3544235 := bstep (se 1 (by rfl) ⟨2658176, by rfl⟩ : syracuseStep 3544235 = 5316353) B5316353
theorem B2659499 : Blo 698317 2659499 := bstep (se 1 (by rfl) ⟨1994624, by rfl⟩ : syracuseStep 2659499 = 3989249) B3989249
theorem B1185097 : Blo 698317 1185097 := bstep (se 2 (by rfl) ⟨444411, by rfl⟩ : syracuseStep 1185097 = 888823) B888823
theorem B1185131 : Blo 698317 1185131 := bstep (se 1 (by rfl) ⟨888848, by rfl⟩ : syracuseStep 1185131 = 1777697) B1777697
theorem B1578383 : Blo 698317 1578383 := bstep (se 1 (by rfl) ⟨1183787, by rfl⟩ : syracuseStep 1578383 = 2367575) B2367575
theorem B3544721 : Blo 698317 3544721 := bstep (se 2 (by rfl) ⟨1329270, by rfl⟩ : syracuseStep 3544721 = 2658541) B2658541
theorem B1578707 : Blo 698317 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B11540333 : Blo 698317 11540333 := bstep (se 3 (by rfl) ⟨2163812, by rfl⟩ : syracuseStep 11540333 = 4327625) B4327625
theorem B21502343 : Blo 698317 21502343 := bstep (se 1 (by rfl) ⟨16126757, by rfl⟩ : syracuseStep 21502343 = 32253515) B32253515
theorem B1579643 : Blo 698317 1579643 := bstep (se 1 (by rfl) ⟨1184732, by rfl⟩ : syracuseStep 1579643 = 2369465) B2369465
theorem B8985289 : Blo 698317 8985289 := bstep (se 2 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 8985289 = 6738967) B6738967
theorem B1579769 : Blo 698317 1579769 := bstep (se 2 (by rfl) ⟨592413, by rfl⟩ : syracuseStep 1579769 = 1184827) B1184827
theorem B2562911 : Blo 698317 2562911 := bstep (se 1 (by rfl) ⟨1922183, by rfl⟩ : syracuseStep 2562911 = 3844367) B3844367
theorem B1580039 : Blo 698317 1580039 := bstep (se 1 (by rfl) ⟨1185029, by rfl⟩ : syracuseStep 1580039 = 2370059) B2370059
theorem B1580111 : Blo 698317 1580111 := bstep (se 1 (by rfl) ⟨1185083, by rfl⟩ : syracuseStep 1580111 = 2370167) B2370167
theorem B2661457 : Blo 698317 2661457 := bstep (se 2 (by rfl) ⟨998046, by rfl⟩ : syracuseStep 2661457 = 1996093) B1996093
theorem B1678583 : Blo 698317 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B2366711 : Blo 698317 2366711 := bstep (se 1 (by rfl) ⟨1775033, by rfl⟩ : syracuseStep 2366711 = 3550067) B3550067
theorem B1776887 : Blo 698317 1776887 := bstep (se 1 (by rfl) ⟨1332665, by rfl⟩ : syracuseStep 1776887 = 2665331) B2665331
theorem B2661761 : Blo 698317 2661761 := bstep (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) B1996321
theorem B2367035 : Blo 698317 2367035 := bstep (se 1 (by rfl) ⟨1775276, by rfl⟩ : syracuseStep 2367035 = 3550553) B3550553
theorem B6725207 : Blo 698317 6725207 := bstep (se 1 (by rfl) ⟨5043905, by rfl⟩ : syracuseStep 6725207 = 10087811) B10087811
theorem B2662217 : Blo 698317 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B2367305 : Blo 698317 2367305 := bstep (se 2 (by rfl) ⟨887739, by rfl⟩ : syracuseStep 2367305 = 1775479) B1775479
theorem B4857695 : Blo 698317 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B2531179 : Blo 698317 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B3546989 : Blo 698317 3546989 := bstep (se 3 (by rfl) ⟨665060, by rfl⟩ : syracuseStep 3546989 = 1330121) B1330121
theorem B3547151 : Blo 698317 3547151 := bstep (se 1 (by rfl) ⟨2660363, by rfl⟩ : syracuseStep 3547151 = 5320727) B5320727
theorem B2662415 : Blo 698317 2662415 := bstep (se 1 (by rfl) ⟨1996811, by rfl⟩ : syracuseStep 2662415 = 3993623) B3993623
theorem B21537089 : Blo 698317 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B19178009 : Blo 698317 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B5055149 : Blo 698317 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B1418057 : Blo 698317 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B2237291 : Blo 698317 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B5677931 : Blo 698317 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B2564983 : Blo 698317 2564983 := bstep (se 1 (by rfl) ⟨1923737, by rfl⟩ : syracuseStep 2564983 = 3847475) B3847475
theorem B2368439 : Blo 698317 2368439 := bstep (se 1 (by rfl) ⟨1776329, by rfl⟩ : syracuseStep 2368439 = 3552659) B3552659
theorem B4268983 : Blo 698317 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B8954945 : Blo 698317 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B2369033 : Blo 698317 2369033 := bstep (se 2 (by rfl) ⟨888387, by rfl⟩ : syracuseStep 2369033 = 1776775) B1776775
theorem B1123879 : Blo 698317 1123879 := bstep (se 1 (by rfl) ⟨842909, by rfl⟩ : syracuseStep 1123879 = 1685819) B1685819
theorem B8496701 : Blo 698317 8496701 := bstep (se 3 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 8496701 = 3186263) B3186263
theorem B698331 : Blo 698317 698331 := bstep (se 1 (by rfl) ⟨523748, by rfl⟩ : syracuseStep 698331 = 1047497) B1047497
theorem B15542279 : Blo 698317 15542279 := bstep (se 1 (by rfl) ⟨11656709, by rfl⟩ : syracuseStep 15542279 = 23313419) B23313419
theorem B698407 : Blo 698317 698407 := bstep (se 1 (by rfl) ⟨523805, by rfl⟩ : syracuseStep 698407 = 1047611) B1047611
theorem B698447 : Blo 698317 698447 := bstep (se 1 (by rfl) ⟨523835, by rfl⟩ : syracuseStep 698447 = 1047671) B1047671
theorem B698463 : Blo 698317 698463 := bstep (se 1 (by rfl) ⟨523847, by rfl⟩ : syracuseStep 698463 = 1047695) B1047695
theorem B698491 : Blo 698317 698491 := bstep (se 1 (by rfl) ⟨523868, by rfl⟩ : syracuseStep 698491 = 1047737) B1047737
theorem B698543 : Blo 698317 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B698567 : Blo 698317 698567 := bstep (se 1 (by rfl) ⟨523925, by rfl⟩ : syracuseStep 698567 = 1047851) B1047851
theorem B698587 : Blo 698317 698587 := bstep (se 1 (by rfl) ⟨523940, by rfl⟩ : syracuseStep 698587 = 1047881) B1047881
theorem B698663 : Blo 698317 698663 := bstep (se 1 (by rfl) ⟨523997, by rfl⟩ : syracuseStep 698663 = 1047995) B1047995
theorem B7579955 : Blo 698317 7579955 := bstep (se 1 (by rfl) ⟨5684966, by rfl⟩ : syracuseStep 7579955 = 11369933) B11369933
theorem B698703 : Blo 698317 698703 := bstep (se 1 (by rfl) ⟨524027, by rfl⟩ : syracuseStep 698703 = 1048055) B1048055
theorem B698719 : Blo 698317 698719 := bstep (se 1 (by rfl) ⟨524039, by rfl⟩ : syracuseStep 698719 = 1048079) B1048079
theorem B2369897 : Blo 698317 2369897 := bstep (se 2 (by rfl) ⟨888711, by rfl⟩ : syracuseStep 2369897 = 1777423) B1777423
theorem B698747 : Blo 698317 698747 := bstep (se 1 (by rfl) ⟨524060, by rfl⟩ : syracuseStep 698747 = 1048121) B1048121
theorem B5122457 : Blo 698317 5122457 := bstep (se 2 (by rfl) ⟨1920921, by rfl⟩ : syracuseStep 5122457 = 3841843) B3841843
theorem B698799 : Blo 698317 698799 := bstep (se 1 (by rfl) ⟨524099, by rfl⟩ : syracuseStep 698799 = 1048199) B1048199
theorem B698823 : Blo 698317 698823 := bstep (se 1 (by rfl) ⟨524117, by rfl⟩ : syracuseStep 698823 = 1048235) B1048235
theorem B698843 : Blo 698317 698843 := bstep (se 1 (by rfl) ⟨524132, by rfl⟩ : syracuseStep 698843 = 1048265) B1048265
theorem B3779081 : Blo 698317 3779081 := bstep (se 2 (by rfl) ⟨1417155, by rfl⟩ : syracuseStep 3779081 = 2834311) B2834311
theorem B698919 : Blo 698317 698919 := bstep (se 1 (by rfl) ⟨524189, by rfl⟩ : syracuseStep 698919 = 1048379) B1048379
theorem B1419815 : Blo 698317 1419815 := bstep (se 1 (by rfl) ⟨1064861, by rfl⟩ : syracuseStep 1419815 = 2129723) B2129723
theorem B698959 : Blo 698317 698959 := bstep (se 1 (by rfl) ⟨524219, by rfl⟩ : syracuseStep 698959 = 1048439) B1048439
theorem B698975 : Blo 698317 698975 := bstep (se 1 (by rfl) ⟨524231, by rfl⟩ : syracuseStep 698975 = 1048463) B1048463
theorem B699003 : Blo 698317 699003 := bstep (se 1 (by rfl) ⟨524252, by rfl⟩ : syracuseStep 699003 = 1048505) B1048505
theorem B699055 : Blo 698317 699055 := bstep (se 1 (by rfl) ⟨524291, by rfl⟩ : syracuseStep 699055 = 1048583) B1048583
theorem B699079 : Blo 698317 699079 := bstep (se 1 (by rfl) ⟨524309, by rfl⟩ : syracuseStep 699079 = 1048619) B1048619
theorem B5057225 : Blo 698317 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B3549905 : Blo 698317 3549905 := bstep (se 2 (by rfl) ⟨1331214, by rfl⟩ : syracuseStep 3549905 = 2662429) B2662429
theorem B699099 : Blo 698317 699099 := bstep (se 1 (by rfl) ⟨524324, by rfl⟩ : syracuseStep 699099 = 1048649) B1048649
theorem B699175 : Blo 698317 699175 := bstep (se 1 (by rfl) ⟨524381, by rfl⟩ : syracuseStep 699175 = 1048763) B1048763
theorem B699215 : Blo 698317 699215 := bstep (se 1 (by rfl) ⟨524411, by rfl⟩ : syracuseStep 699215 = 1048823) B1048823
theorem B699231 : Blo 698317 699231 := bstep (se 1 (by rfl) ⟨524423, by rfl⟩ : syracuseStep 699231 = 1048847) B1048847
theorem B699259 : Blo 698317 699259 := bstep (se 1 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 699259 = 1048889) B1048889
theorem B699311 : Blo 698317 699311 := bstep (se 1 (by rfl) ⟨524483, by rfl⟩ : syracuseStep 699311 = 1048967) B1048967
theorem B699335 : Blo 698317 699335 := bstep (se 1 (by rfl) ⟨524501, by rfl⟩ : syracuseStep 699335 = 1049003) B1049003
theorem B699355 : Blo 698317 699355 := bstep (se 1 (by rfl) ⟨524516, by rfl⟩ : syracuseStep 699355 = 1049033) B1049033
theorem B621849635 : Blo 698317 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B699431 : Blo 698317 699431 := bstep (se 1 (by rfl) ⟨524573, by rfl⟩ : syracuseStep 699431 = 1049147) B1049147
theorem B699471 : Blo 698317 699471 := bstep (se 1 (by rfl) ⟨524603, by rfl⟩ : syracuseStep 699471 = 1049207) B1049207
theorem B699487 : Blo 698317 699487 := bstep (se 1 (by rfl) ⟨524615, by rfl⟩ : syracuseStep 699487 = 1049231) B1049231
theorem B699515 : Blo 698317 699515 := bstep (se 1 (by rfl) ⟨524636, by rfl⟩ : syracuseStep 699515 = 1049273) B1049273
theorem B699567 : Blo 698317 699567 := bstep (se 1 (by rfl) ⟨524675, by rfl⟩ : syracuseStep 699567 = 1049351) B1049351
theorem B699591 : Blo 698317 699591 := bstep (se 1 (by rfl) ⟨524693, by rfl⟩ : syracuseStep 699591 = 1049387) B1049387
theorem B699611 : Blo 698317 699611 := bstep (se 1 (by rfl) ⟨524708, by rfl⟩ : syracuseStep 699611 = 1049417) B1049417
theorem B699687 : Blo 698317 699687 := bstep (se 1 (by rfl) ⟨524765, by rfl⟩ : syracuseStep 699687 = 1049531) B1049531
theorem B699727 : Blo 698317 699727 := bstep (se 1 (by rfl) ⟨524795, by rfl⟩ : syracuseStep 699727 = 1049591) B1049591
theorem B699743 : Blo 698317 699743 := bstep (se 1 (by rfl) ⟨524807, by rfl⟩ : syracuseStep 699743 = 1049615) B1049615
theorem B34614641 : Blo 698317 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B699771 : Blo 698317 699771 := bstep (se 1 (by rfl) ⟨524828, by rfl⟩ : syracuseStep 699771 = 1049657) B1049657
theorem B699823 : Blo 698317 699823 := bstep (se 1 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 699823 = 1049735) B1049735
theorem B699847 : Blo 698317 699847 := bstep (se 1 (by rfl) ⟨524885, by rfl⟩ : syracuseStep 699847 = 1049771) B1049771
theorem B699867 : Blo 698317 699867 := bstep (se 1 (by rfl) ⟨524900, by rfl⟩ : syracuseStep 699867 = 1049801) B1049801
theorem B8957405 : Blo 698317 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B699943 : Blo 698317 699943 := bstep (se 1 (by rfl) ⟨524957, by rfl⟩ : syracuseStep 699943 = 1049915) B1049915
theorem B699983 : Blo 698317 699983 := bstep (se 1 (by rfl) ⟨524987, by rfl⟩ : syracuseStep 699983 = 1049975) B1049975
theorem B699999 : Blo 698317 699999 := bstep (se 1 (by rfl) ⟨524999, by rfl⟩ : syracuseStep 699999 = 1049999) B1049999
theorem B700027 : Blo 698317 700027 := bstep (se 1 (by rfl) ⟨525020, by rfl⟩ : syracuseStep 700027 = 1050041) B1050041
theorem B700079 : Blo 698317 700079 := bstep (se 1 (by rfl) ⟨525059, by rfl⟩ : syracuseStep 700079 = 1050119) B1050119
theorem B700103 : Blo 698317 700103 := bstep (se 1 (by rfl) ⟨525077, by rfl⟩ : syracuseStep 700103 = 1050155) B1050155
theorem B700123 : Blo 698317 700123 := bstep (se 1 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 700123 = 1050185) B1050185
theorem B700199 : Blo 698317 700199 := bstep (se 1 (by rfl) ⟨525149, by rfl⟩ : syracuseStep 700199 = 1050299) B1050299
theorem B700239 : Blo 698317 700239 := bstep (se 1 (by rfl) ⟨525179, by rfl⟩ : syracuseStep 700239 = 1050359) B1050359
theorem B700255 : Blo 698317 700255 := bstep (se 1 (by rfl) ⟨525191, by rfl⟩ : syracuseStep 700255 = 1050383) B1050383
theorem B700283 : Blo 698317 700283 := bstep (se 1 (by rfl) ⟨525212, by rfl⟩ : syracuseStep 700283 = 1050425) B1050425
theorem B700335 : Blo 698317 700335 := bstep (se 1 (by rfl) ⟨525251, by rfl⟩ : syracuseStep 700335 = 1050503) B1050503
theorem B700359 : Blo 698317 700359 := bstep (se 1 (by rfl) ⟨525269, by rfl⟩ : syracuseStep 700359 = 1050539) B1050539
theorem B700379 : Blo 698317 700379 := bstep (se 1 (by rfl) ⟨525284, by rfl⟩ : syracuseStep 700379 = 1050569) B1050569
theorem B2240531 : Blo 698317 2240531 := bstep (se 1 (by rfl) ⟨1680398, by rfl⟩ : syracuseStep 2240531 = 3360797) B3360797
theorem B700455 : Blo 698317 700455 := bstep (se 1 (by rfl) ⟨525341, by rfl⟩ : syracuseStep 700455 = 1050683) B1050683
theorem B700495 : Blo 698317 700495 := bstep (se 1 (by rfl) ⟨525371, by rfl⟩ : syracuseStep 700495 = 1050743) B1050743
theorem B700511 : Blo 698317 700511 := bstep (se 1 (by rfl) ⟨525383, by rfl⟩ : syracuseStep 700511 = 1050767) B1050767
theorem B700539 : Blo 698317 700539 := bstep (se 1 (by rfl) ⟨525404, by rfl⟩ : syracuseStep 700539 = 1050809) B1050809
theorem B700591 : Blo 698317 700591 := bstep (se 1 (by rfl) ⟨525443, by rfl⟩ : syracuseStep 700591 = 1050887) B1050887
theorem B700615 : Blo 698317 700615 := bstep (se 1 (by rfl) ⟨525461, by rfl⟩ : syracuseStep 700615 = 1050923) B1050923
theorem B700635 : Blo 698317 700635 := bstep (se 1 (by rfl) ⟨525476, by rfl⟩ : syracuseStep 700635 = 1050953) B1050953
theorem B700711 : Blo 698317 700711 := bstep (se 1 (by rfl) ⟨525533, by rfl⟩ : syracuseStep 700711 = 1051067) B1051067
theorem B700751 : Blo 698317 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B700767 : Blo 698317 700767 := bstep (se 1 (by rfl) ⟨525575, by rfl⟩ : syracuseStep 700767 = 1051151) B1051151
theorem B995689 : Blo 698317 995689 := bstep (se 2 (by rfl) ⟨373383, by rfl⟩ : syracuseStep 995689 = 746767) B746767
theorem B700795 : Blo 698317 700795 := bstep (se 1 (by rfl) ⟨525596, by rfl⟩ : syracuseStep 700795 = 1051193) B1051193
theorem B700847 : Blo 698317 700847 := bstep (se 1 (by rfl) ⟨525635, by rfl⟩ : syracuseStep 700847 = 1051271) B1051271
theorem B700871 : Blo 698317 700871 := bstep (se 1 (by rfl) ⟨525653, by rfl⟩ : syracuseStep 700871 = 1051307) B1051307
theorem B700891 : Blo 698317 700891 := bstep (se 1 (by rfl) ⟨525668, by rfl⟩ : syracuseStep 700891 = 1051337) B1051337
theorem B700967 : Blo 698317 700967 := bstep (se 1 (by rfl) ⟨525725, by rfl⟩ : syracuseStep 700967 = 1051451) B1051451
theorem B2241083 : Blo 698317 2241083 := bstep (se 1 (by rfl) ⟨1680812, by rfl⟩ : syracuseStep 2241083 = 3361625) B3361625
theorem B701007 : Blo 698317 701007 := bstep (se 1 (by rfl) ⟨525755, by rfl⟩ : syracuseStep 701007 = 1051511) B1051511
theorem B701023 : Blo 698317 701023 := bstep (se 1 (by rfl) ⟨525767, by rfl⟩ : syracuseStep 701023 = 1051535) B1051535
theorem B2241121 : Blo 698317 2241121 := bstep (se 2 (by rfl) ⟨840420, by rfl⟩ : syracuseStep 2241121 = 1680841) B1680841
theorem B701051 : Blo 698317 701051 := bstep (se 1 (by rfl) ⟨525788, by rfl⟩ : syracuseStep 701051 = 1051577) B1051577
theorem B2994823 : Blo 698317 2994823 := bstep (se 1 (by rfl) ⟨2246117, by rfl⟩ : syracuseStep 2994823 = 4492235) B4492235
theorem B701103 : Blo 698317 701103 := bstep (se 1 (by rfl) ⟨525827, by rfl⟩ : syracuseStep 701103 = 1051655) B1051655
theorem B701127 : Blo 698317 701127 := bstep (se 1 (by rfl) ⟨525845, by rfl⟩ : syracuseStep 701127 = 1051691) B1051691
theorem B3846865 : Blo 698317 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B701147 : Blo 698317 701147 := bstep (se 1 (by rfl) ⟨525860, by rfl⟩ : syracuseStep 701147 = 1051721) B1051721
theorem B701223 : Blo 698317 701223 := bstep (se 1 (by rfl) ⟨525917, by rfl⟩ : syracuseStep 701223 = 1051835) B1051835
theorem B701263 : Blo 698317 701263 := bstep (se 1 (by rfl) ⟨525947, by rfl⟩ : syracuseStep 701263 = 1051895) B1051895
theorem B701279 : Blo 698317 701279 := bstep (se 1 (by rfl) ⟨525959, by rfl⟩ : syracuseStep 701279 = 1051919) B1051919
theorem B701307 : Blo 698317 701307 := bstep (se 1 (by rfl) ⟨525980, by rfl⟩ : syracuseStep 701307 = 1051961) B1051961
theorem B701359 : Blo 698317 701359 := bstep (se 1 (by rfl) ⟨526019, by rfl⟩ : syracuseStep 701359 = 1052039) B1052039
theorem B701383 : Blo 698317 701383 := bstep (se 1 (by rfl) ⟨526037, by rfl⟩ : syracuseStep 701383 = 1052075) B1052075
theorem B701403 : Blo 698317 701403 := bstep (se 1 (by rfl) ⟨526052, by rfl⟩ : syracuseStep 701403 = 1052105) B1052105
theorem B701479 : Blo 698317 701479 := bstep (se 1 (by rfl) ⟨526109, by rfl⟩ : syracuseStep 701479 = 1052219) B1052219
theorem B701519 : Blo 698317 701519 := bstep (se 1 (by rfl) ⟨526139, by rfl⟩ : syracuseStep 701519 = 1052279) B1052279
theorem B3552335 : Blo 698317 3552335 := bstep (se 1 (by rfl) ⟨2664251, by rfl⟩ : syracuseStep 3552335 = 5328503) B5328503
theorem B701535 : Blo 698317 701535 := bstep (se 1 (by rfl) ⟨526151, by rfl⟩ : syracuseStep 701535 = 1052303) B1052303
theorem B996475 : Blo 698317 996475 := bstep (se 1 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 996475 = 1494713) B1494713
theorem B701563 : Blo 698317 701563 := bstep (se 1 (by rfl) ⟨526172, by rfl⟩ : syracuseStep 701563 = 1052345) B1052345
theorem B2733209 : Blo 698317 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B36353195 : Blo 698317 36353195 := bstep (se 1 (by rfl) ⟨27264896, by rfl⟩ : syracuseStep 36353195 = 54529793) B54529793
theorem B701615 : Blo 698317 701615 := bstep (se 1 (by rfl) ⟨526211, by rfl⟩ : syracuseStep 701615 = 1052423) B1052423
theorem B701639 : Blo 698317 701639 := bstep (se 1 (by rfl) ⟨526229, by rfl⟩ : syracuseStep 701639 = 1052459) B1052459
theorem B701659 : Blo 698317 701659 := bstep (se 1 (by rfl) ⟨526244, by rfl⟩ : syracuseStep 701659 = 1052489) B1052489
theorem B701735 : Blo 698317 701735 := bstep (se 1 (by rfl) ⟨526301, by rfl⟩ : syracuseStep 701735 = 1052603) B1052603
theorem B701775 : Blo 698317 701775 := bstep (se 1 (by rfl) ⟨526331, by rfl⟩ : syracuseStep 701775 = 1052663) B1052663
theorem B701791 : Blo 698317 701791 := bstep (se 1 (by rfl) ⟨526343, by rfl⟩ : syracuseStep 701791 = 1052687) B1052687
theorem B701819 : Blo 698317 701819 := bstep (se 1 (by rfl) ⟨526364, by rfl⟩ : syracuseStep 701819 = 1052729) B1052729
theorem B701871 : Blo 698317 701871 := bstep (se 1 (by rfl) ⟨526403, by rfl⟩ : syracuseStep 701871 = 1052807) B1052807
theorem B701895 : Blo 698317 701895 := bstep (se 1 (by rfl) ⟨526421, by rfl⟩ : syracuseStep 701895 = 1052843) B1052843
theorem B5322185 : Blo 698317 5322185 := bstep (se 2 (by rfl) ⟨1995819, by rfl⟩ : syracuseStep 5322185 = 3991639) B3991639
theorem B701915 : Blo 698317 701915 := bstep (se 1 (by rfl) ⟨526436, by rfl⟩ : syracuseStep 701915 = 1052873) B1052873
theorem B2831881 : Blo 698317 2831881 := bstep (se 2 (by rfl) ⟨1061955, by rfl⟩ : syracuseStep 2831881 = 2123911) B2123911
theorem B3978791 : Blo 698317 3978791 := bstep (se 1 (by rfl) ⟨2984093, by rfl⟩ : syracuseStep 3978791 = 5968187) B5968187
theorem B701991 : Blo 698317 701991 := bstep (se 1 (by rfl) ⟨526493, by rfl⟩ : syracuseStep 701991 = 1052987) B1052987
theorem B702031 : Blo 698317 702031 := bstep (se 1 (by rfl) ⟨526523, by rfl⟩ : syracuseStep 702031 = 1053047) B1053047
theorem B702047 : Blo 698317 702047 := bstep (se 1 (by rfl) ⟨526535, by rfl⟩ : syracuseStep 702047 = 1053071) B1053071
theorem B2242171 : Blo 698317 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B702075 : Blo 698317 702075 := bstep (se 1 (by rfl) ⟨526556, by rfl⟩ : syracuseStep 702075 = 1053113) B1053113
theorem B702127 : Blo 698317 702127 := bstep (se 1 (by rfl) ⟨526595, by rfl⟩ : syracuseStep 702127 = 1053191) B1053191
theorem B702151 : Blo 698317 702151 := bstep (se 1 (by rfl) ⟨526613, by rfl⟩ : syracuseStep 702151 = 1053227) B1053227
theorem B3552983 : Blo 698317 3552983 := bstep (se 1 (by rfl) ⟨2664737, by rfl⟩ : syracuseStep 3552983 = 5329475) B5329475
theorem B702171 : Blo 698317 702171 := bstep (se 1 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 702171 = 1053257) B1053257
theorem B702247 : Blo 698317 702247 := bstep (se 1 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 702247 = 1053371) B1053371
theorem B702287 : Blo 698317 702287 := bstep (se 1 (by rfl) ⟨526715, by rfl⟩ : syracuseStep 702287 = 1053431) B1053431
theorem B3192671 : Blo 698317 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B702303 : Blo 698317 702303 := bstep (se 1 (by rfl) ⟨526727, by rfl⟩ : syracuseStep 702303 = 1053455) B1053455
theorem B3782713 : Blo 698317 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B3356761 : Blo 698317 3356761 := bstep (se 2 (by rfl) ⟨1258785, by rfl⟩ : syracuseStep 3356761 = 2517571) B2517571
theorem B2996585 : Blo 698317 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B997967 : Blo 698317 997967 := bstep (se 1 (by rfl) ⟨748475, by rfl⟩ : syracuseStep 997967 = 1496951) B1496951
theorem B1326203 : Blo 698317 1326203 := bstep (se 1 (by rfl) ⟨994652, by rfl⟩ : syracuseStep 1326203 = 1989305) B1989305
theorem B1326431 : Blo 698317 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B2243965 : Blo 698317 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B21052853 : Blo 698317 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B5684681 : Blo 698317 5684681 := bstep (se 2 (by rfl) ⟨2131755, by rfl⟩ : syracuseStep 5684681 = 4263511) B4263511
theorem B1687049 : Blo 698317 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B1326689 : Blo 698317 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B1326955 : Blo 698317 1326955 := bstep (se 1 (by rfl) ⟨995216, by rfl⟩ : syracuseStep 1326955 = 1990433) B1990433
theorem B2834603 : Blo 698317 2834603 := bstep (se 1 (by rfl) ⟨2125952, by rfl⟩ : syracuseStep 2834603 = 4251905) B4251905
theorem B24264971 : Blo 698317 24264971 := bstep (se 1 (by rfl) ⟨18198728, by rfl⟩ : syracuseStep 24264971 = 36397457) B36397457
theorem B1196383 : Blo 698317 1196383 := bstep (se 1 (by rfl) ⟨897287, by rfl⟩ : syracuseStep 1196383 = 1794575) B1794575
theorem B2834831 : Blo 698317 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B3981959 : Blo 698317 3981959 := bstep (se 1 (by rfl) ⟨2986469, by rfl⟩ : syracuseStep 3981959 = 5972939) B5972939
theorem B1328147 : Blo 698317 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B1328375 : Blo 698317 1328375 := bstep (se 1 (by rfl) ⟨996281, by rfl⟩ : syracuseStep 1328375 = 1992563) B1992563
theorem B3360143 : Blo 698317 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B1492577 : Blo 698317 1492577 := bstep (se 2 (by rfl) ⟨559716, by rfl⟩ : syracuseStep 1492577 = 1119433) B1119433
theorem B3983417 : Blo 698317 3983417 := bstep (se 2 (by rfl) ⟨1493781, by rfl⟩ : syracuseStep 3983417 = 2987563) B2987563
theorem B5130497 : Blo 698317 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B3787019 : Blo 698317 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B2247041 : Blo 698317 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B1329787 : Blo 698317 1329787 := bstep (se 1 (by rfl) ⟨997340, by rfl⟩ : syracuseStep 1329787 = 1994681) B1994681
theorem B22727303 : Blo 698317 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B1330015 : Blo 698317 1330015 := bstep (se 1 (by rfl) ⟨997511, by rfl⟩ : syracuseStep 1330015 = 1995023) B1995023
theorem B1198955 : Blo 698317 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B20237201 : Blo 698317 20237201 := bstep (se 2 (by rfl) ⟨7588950, by rfl⟩ : syracuseStep 20237201 = 15177901) B15177901
theorem B1264567 : Blo 698317 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B1330273 : Blo 698317 1330273 := bstep (se 2 (by rfl) ⟨498852, by rfl⟩ : syracuseStep 1330273 = 997705) B997705
theorem B1330607 : Blo 698317 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B1232315 : Blo 698317 1232315 := bstep (se 1 (by rfl) ⟨924236, by rfl⟩ : syracuseStep 1232315 = 1848473) B1848473
theorem B1265171 : Blo 698317 1265171 := bstep (se 1 (by rfl) ⟨948878, by rfl⟩ : syracuseStep 1265171 = 1897757) B1897757
theorem B8081117 : Blo 698317 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B4476653 : Blo 698317 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B8998775 : Blo 698317 8998775 := bstep (se 1 (by rfl) ⟨6749081, by rfl⟩ : syracuseStep 8998775 = 13498163) B13498163
theorem B2248631 : Blo 698317 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B1036327 : Blo 698317 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B1331731 : Blo 698317 1331731 := bstep (se 1 (by rfl) ⟨998798, by rfl⟩ : syracuseStep 1331731 = 1997597) B1997597
theorem B1331959 : Blo 698317 1331959 := bstep (se 1 (by rfl) ⟨998969, by rfl⟩ : syracuseStep 1331959 = 1997939) B1997939
theorem B5690387 : Blo 698317 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B1332263 : Blo 698317 1332263 := bstep (se 1 (by rfl) ⟨999197, by rfl⟩ : syracuseStep 1332263 = 1998395) B1998395
theorem B709807 : Blo 698317 709807 := bstep (se 1 (by rfl) ⟨532355, by rfl⟩ : syracuseStep 709807 = 1064711) B1064711
theorem B3987083 : Blo 698317 3987083 := bstep (se 1 (by rfl) ⟨2990312, by rfl⟩ : syracuseStep 3987083 = 5980625) B5980625
theorem B2873017 : Blo 698317 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B11949767 : Blo 698317 11949767 := bstep (se 1 (by rfl) ⟨8962325, by rfl⟩ : syracuseStep 11949767 = 17924651) B17924651
theorem B3791233 : Blo 698317 3791233 := bstep (se 2 (by rfl) ⟨1421712, by rfl⟩ : syracuseStep 3791233 = 2843425) B2843425
theorem B5036525 : Blo 698317 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B8510285 : Blo 698317 8510285 := bstep (se 3 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 8510285 = 3191357) B3191357
theorem B6740813 : Blo 698317 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B11984759 : Blo 698317 11984759 := bstep (se 1 (by rfl) ⟨8988569, by rfl⟩ : syracuseStep 11984759 = 17977139) B17977139
theorem B1139279 : Blo 698317 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B2024185 : Blo 698317 2024185 := bstep (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) B1518139
theorem B3990455 : Blo 698317 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B6382745 : Blo 698317 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B1992289 : Blo 698317 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B3991457 : Blo 698317 3991457 := bstep (se 2 (by rfl) ⟨1496796, by rfl⟩ : syracuseStep 3991457 = 2993593) B2993593
theorem B3991913 : Blo 698317 3991913 := bstep (se 2 (by rfl) ⟨1496967, by rfl⟩ : syracuseStep 3991913 = 2993935) B2993935
theorem B5106349 : Blo 698317 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B1993405 : Blo 698317 1993405 := bstep (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) B747527
theorem B2517803 : Blo 698317 2517803 := bstep (se 1 (by rfl) ⟨1888352, by rfl⟩ : syracuseStep 2517803 = 3776705) B3776705
theorem B1993747 : Blo 698317 1993747 := bstep (se 1 (by rfl) ⟨1495310, by rfl⟩ : syracuseStep 1993747 = 2990621) B2990621
theorem B5303717 : Blo 698317 5303717 := bstep (se 4 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 5303717 = 994447) B994447
theorem B4484753 : Blo 698317 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B19165091 : Blo 698317 19165091 := bstep (se 1 (by rfl) ⟨14373818, by rfl⟩ : syracuseStep 19165091 = 28747637) B28747637
theorem B1995137 : Blo 698317 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B2519561 : Blo 698317 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B2519675 : Blo 698317 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B1995479 : Blo 698317 1995479 := bstep (se 1 (by rfl) ⟨1496609, by rfl⟩ : syracuseStep 1995479 = 2993219) B2993219
theorem B5993473 : Blo 698317 5993473 := bstep (se 2 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 5993473 = 4495105) B4495105
theorem B3995081 : Blo 698317 3995081 := bstep (se 2 (by rfl) ⟨1498155, by rfl⟩ : syracuseStep 3995081 = 2996311) B2996311
theorem B2356883 : Blo 698317 2356883 := bstep (se 1 (by rfl) ⟨1767662, by rfl⟩ : syracuseStep 2356883 = 3535325) B3535325
theorem B2357099 : Blo 698317 2357099 := bstep (se 1 (by rfl) ⟨1767824, by rfl⟩ : syracuseStep 2357099 = 3535649) B3535649
theorem B2652011 : Blo 698317 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B2357153 : Blo 698317 2357153 := bstep (se 2 (by rfl) ⟨883932, by rfl⟩ : syracuseStep 2357153 = 1767865) B1767865
theorem B30275531 : Blo 698317 30275531 := bstep (se 1 (by rfl) ⟨22706648, by rfl⟩ : syracuseStep 30275531 = 45413297) B45413297
theorem B10123213 : Blo 698317 10123213 := bstep (se 3 (by rfl) ⟨1898102, by rfl⟩ : syracuseStep 10123213 = 3796205) B3796205
theorem B20510765 : Blo 698317 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B9599077 : Blo 698317 9599077 := bstep (se 4 (by rfl) ⟨899913, by rfl⟩ : syracuseStep 9599077 = 1799827) B1799827
theorem B1079735 : Blo 698317 1079735 := bstep (se 1 (by rfl) ⟨809801, by rfl⟩ : syracuseStep 1079735 = 1619603) B1619603
theorem B1571291 : Blo 698317 1571291 := bstep (se 1 (by rfl) ⟨1178468, by rfl⟩ : syracuseStep 1571291 = 2356937) B2356937
theorem B2357747 : Blo 698317 2357747 := bstep (se 1 (by rfl) ⟨1768310, by rfl⟩ : syracuseStep 2357747 = 3536621) B3536621
theorem B3537593 : Blo 698317 3537593 := bstep (se 2 (by rfl) ⟨1326597, by rfl⟩ : syracuseStep 3537593 = 2653195) B2653195
theorem B1178543 : Blo 698317 1178543 := bstep (se 1 (by rfl) ⟨883907, by rfl⟩ : syracuseStep 1178543 = 1767815) B1767815
theorem B1571759 : Blo 698317 1571759 := bstep (se 1 (by rfl) ⟨1178819, by rfl⟩ : syracuseStep 1571759 = 2357639) B2357639
theorem B1047479 : Blo 698317 1047479 := bstep (se 1 (by rfl) ⟨785609, by rfl⟩ : syracuseStep 1047479 = 1571219) B1571219
theorem B1047515 : Blo 698317 1047515 := bstep (se 1 (by rfl) ⟨785636, by rfl⟩ : syracuseStep 1047515 = 1571273) B1571273
theorem B2358287 : Blo 698317 2358287 := bstep (se 1 (by rfl) ⟨1768715, by rfl⟩ : syracuseStep 2358287 = 3537431) B3537431
theorem B2522269 : Blo 698317 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B1572011 : Blo 698317 1572011 := bstep (se 1 (by rfl) ⟨1179008, by rfl⟩ : syracuseStep 1572011 = 2358017) B2358017
theorem B1211591 : Blo 698317 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B1178975 : Blo 698317 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B2391439 : Blo 698317 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B785839 : Blo 698317 785839 := bstep (se 1 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 785839 = 1178759) B1178759
theorem B1047983 : Blo 698317 1047983 := bstep (se 1 (by rfl) ⟨785987, by rfl⟩ : syracuseStep 1047983 = 1571975) B1571975
theorem B1048073 : Blo 698317 1048073 := bstep (se 2 (by rfl) ⟨393027, by rfl⟩ : syracuseStep 1048073 = 786055) B786055
theorem B1048103 : Blo 698317 1048103 := bstep (se 1 (by rfl) ⟨786077, by rfl⟩ : syracuseStep 1048103 = 1572155) B1572155
theorem B1768999 : Blo 698317 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B2358881 : Blo 698317 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B1048187 : Blo 698317 1048187 := bstep (se 1 (by rfl) ⟨786140, by rfl⟩ : syracuseStep 1048187 = 1572281) B1572281
theorem B1572551 : Blo 698317 1572551 := bstep (se 1 (by rfl) ⟨1179413, by rfl⟩ : syracuseStep 1572551 = 2358827) B2358827
theorem B1048313 : Blo 698317 1048313 := bstep (se 2 (by rfl) ⟨393117, by rfl⟩ : syracuseStep 1048313 = 786235) B786235
theorem B786271 : Blo 698317 786271 := bstep (se 1 (by rfl) ⟨589703, by rfl⟩ : syracuseStep 786271 = 1179407) B1179407
theorem B1048415 : Blo 698317 1048415 := bstep (se 1 (by rfl) ⟨786311, by rfl⟩ : syracuseStep 1048415 = 1572623) B1572623
theorem B1048427 : Blo 698317 1048427 := bstep (se 1 (by rfl) ⟨786320, by rfl⟩ : syracuseStep 1048427 = 1572641) B1572641
theorem B1769323 : Blo 698317 1769323 := bstep (se 1 (by rfl) ⟨1326992, by rfl⟩ : syracuseStep 1769323 = 2653985) B2653985
theorem B1179535 : Blo 698317 1179535 := bstep (se 1 (by rfl) ⟨884651, by rfl⟩ : syracuseStep 1179535 = 1769303) B1769303
theorem B1179913 : Blo 698317 1179913 := bstep (se 2 (by rfl) ⟨442467, by rfl⟩ : syracuseStep 1179913 = 884935) B884935
theorem B1048841 : Blo 698317 1048841 := bstep (se 2 (by rfl) ⟨393315, by rfl⟩ : syracuseStep 1048841 = 786631) B786631
theorem B1048943 : Blo 698317 1048943 := bstep (se 1 (by rfl) ⟨786707, by rfl⟩ : syracuseStep 1048943 = 1573415) B1573415
theorem B786811 : Blo 698317 786811 := bstep (se 1 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 786811 = 1180217) B1180217
theorem B11993507 : Blo 698317 11993507 := bstep (se 1 (by rfl) ⟨8995130, by rfl⟩ : syracuseStep 11993507 = 17990261) B17990261
theorem B3539375 : Blo 698317 3539375 := bstep (se 1 (by rfl) ⟨2654531, by rfl⟩ : syracuseStep 3539375 = 5309063) B5309063
theorem B2654639 : Blo 698317 2654639 := bstep (se 1 (by rfl) ⟨1990979, by rfl⟩ : syracuseStep 2654639 = 3981959) B3981959
theorem B1049159 : Blo 698317 1049159 := bstep (se 1 (by rfl) ⟨786869, by rfl⟩ : syracuseStep 1049159 = 1573739) B1573739
theorem B1049195 : Blo 698317 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B2359961 : Blo 698317 2359961 := bstep (se 2 (by rfl) ⟨884985, by rfl⟩ : syracuseStep 2359961 = 1769971) B1769971
theorem B1573559 : Blo 698317 1573559 := bstep (se 1 (by rfl) ⟨1180169, by rfl⟩ : syracuseStep 1573559 = 2360339) B2360339
theorem B885431 : Blo 698317 885431 := bstep (se 1 (by rfl) ⟨664073, by rfl⟩ : syracuseStep 885431 = 1328147) B1328147
theorem B1049423 : Blo 698317 1049423 := bstep (se 1 (by rfl) ⟨787067, by rfl⟩ : syracuseStep 1049423 = 1574135) B1574135
theorem B885583 : Blo 698317 885583 := bstep (se 1 (by rfl) ⟨664187, by rfl⟩ : syracuseStep 885583 = 1328375) B1328375
theorem B787279 : Blo 698317 787279 := bstep (se 1 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 787279 = 1180919) B1180919
theorem B1573775 : Blo 698317 1573775 := bstep (se 1 (by rfl) ⟨1180331, by rfl⟩ : syracuseStep 1573775 = 2360663) B2360663
theorem B15598657 : Blo 698317 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B1770619 : Blo 698317 1770619 := bstep (se 1 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 1770619 = 2655929) B2655929
theorem B1049819 : Blo 698317 1049819 := bstep (se 1 (by rfl) ⟨787364, by rfl⟩ : syracuseStep 1049819 = 1574729) B1574729
theorem B787675 : Blo 698317 787675 := bstep (se 1 (by rfl) ⟨590756, by rfl⟩ : syracuseStep 787675 = 1181513) B1181513
theorem B3540347 : Blo 698317 3540347 := bstep (se 1 (by rfl) ⟨2655260, by rfl⟩ : syracuseStep 3540347 = 5310521) B5310521
theorem B2655611 : Blo 698317 2655611 := bstep (se 1 (by rfl) ⟨1991708, by rfl⟩ : syracuseStep 2655611 = 3983417) B3983417
theorem B1049993 : Blo 698317 1049993 := bstep (se 2 (by rfl) ⟨393747, by rfl⟩ : syracuseStep 1049993 = 787495) B787495
theorem B787963 : Blo 698317 787963 := bstep (se 1 (by rfl) ⟨590972, by rfl⟩ : syracuseStep 787963 = 1181945) B1181945
theorem B2524679 : Blo 698317 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B1574495 : Blo 698317 1574495 := bstep (se 1 (by rfl) ⟨1180871, by rfl⟩ : syracuseStep 1574495 = 2361743) B2361743
theorem B788143 : Blo 698317 788143 := bstep (se 1 (by rfl) ⟨591107, by rfl⟩ : syracuseStep 788143 = 1182215) B1182215
theorem B1181371 : Blo 698317 1181371 := bstep (se 1 (by rfl) ⟨886028, by rfl⟩ : syracuseStep 1181371 = 1772057) B1772057
theorem B1050347 : Blo 698317 1050347 := bstep (se 1 (by rfl) ⟨787760, by rfl⟩ : syracuseStep 1050347 = 1575521) B1575521
theorem B1574711 : Blo 698317 1574711 := bstep (se 1 (by rfl) ⟨1181033, by rfl⟩ : syracuseStep 1574711 = 2362067) B2362067
theorem B1050575 : Blo 698317 1050575 := bstep (se 1 (by rfl) ⟨787931, by rfl⟩ : syracuseStep 1050575 = 1575863) B1575863
theorem B788431 : Blo 698317 788431 := bstep (se 1 (by rfl) ⟨591323, by rfl⟩ : syracuseStep 788431 = 1182647) B1182647
theorem B1575017 : Blo 698317 1575017 := bstep (se 2 (by rfl) ⟨590631, by rfl⟩ : syracuseStep 1575017 = 1181263) B1181263
theorem B2656385 : Blo 698317 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B2361473 : Blo 698317 2361473 := bstep (se 2 (by rfl) ⟨885552, by rfl⟩ : syracuseStep 2361473 = 1771105) B1771105
theorem B821543 : Blo 698317 821543 := bstep (se 1 (by rfl) ⟨616157, by rfl⟩ : syracuseStep 821543 = 1232315) B1232315
theorem B1050971 : Blo 698317 1050971 := bstep (se 1 (by rfl) ⟨788228, by rfl⟩ : syracuseStep 1050971 = 1576457) B1576457
theorem B788827 : Blo 698317 788827 := bstep (se 1 (by rfl) ⟨591620, by rfl⟩ : syracuseStep 788827 = 1183241) B1183241
theorem B788935 : Blo 698317 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B2984435 : Blo 698317 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B2361851 : Blo 698317 2361851 := bstep (se 1 (by rfl) ⟨1771388, by rfl⟩ : syracuseStep 2361851 = 3542777) B3542777
theorem B1772027 : Blo 698317 1772027 := bstep (se 1 (by rfl) ⟨1329020, by rfl⟩ : syracuseStep 1772027 = 2658041) B2658041
theorem B1051199 : Blo 698317 1051199 := bstep (se 1 (by rfl) ⟨788399, by rfl⟩ : syracuseStep 1051199 = 1576799) B1576799
theorem B1575503 : Blo 698317 1575503 := bstep (se 1 (by rfl) ⟨1181627, by rfl⟩ : syracuseStep 1575503 = 2363255) B2363255
theorem B5999183 : Blo 698317 5999183 := bstep (se 1 (by rfl) ⟨4499387, by rfl⟩ : syracuseStep 5999183 = 8998775) B8998775
theorem B3541643 : Blo 698317 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B1051319 : Blo 698317 1051319 := bstep (se 1 (by rfl) ⟨788489, by rfl⟩ : syracuseStep 1051319 = 1576979) B1576979
theorem B1575647 : Blo 698317 1575647 := bstep (se 1 (by rfl) ⟨1181735, by rfl⟩ : syracuseStep 1575647 = 2363471) B2363471
theorem B1182431 : Blo 698317 1182431 := bstep (se 1 (by rfl) ⟨886823, by rfl⟩ : syracuseStep 1182431 = 1773647) B1773647
theorem B789295 : Blo 698317 789295 := bstep (se 1 (by rfl) ⟨591971, by rfl⟩ : syracuseStep 789295 = 1183943) B1183943
theorem B1051547 : Blo 698317 1051547 := bstep (se 1 (by rfl) ⟨788660, by rfl⟩ : syracuseStep 1051547 = 1577321) B1577321
theorem B789403 : Blo 698317 789403 := bstep (se 1 (by rfl) ⟨592052, by rfl⟩ : syracuseStep 789403 = 1184105) B1184105
theorem B2362283 : Blo 698317 2362283 := bstep (se 1 (by rfl) ⟨1771712, by rfl⟩ : syracuseStep 2362283 = 3543425) B3543425
theorem B1575899 : Blo 698317 1575899 := bstep (se 1 (by rfl) ⟨1181924, by rfl⟩ : syracuseStep 1575899 = 2363849) B2363849
theorem B1576079 : Blo 698317 1576079 := bstep (se 1 (by rfl) ⟨1182059, by rfl⟩ : syracuseStep 1576079 = 2364119) B2364119
theorem B1182863 : Blo 698317 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B1576169 : Blo 698317 1576169 := bstep (se 2 (by rfl) ⟨591063, by rfl⟩ : syracuseStep 1576169 = 1182127) B1182127
theorem B1576223 : Blo 698317 1576223 := bstep (se 1 (by rfl) ⟨1182167, by rfl⟩ : syracuseStep 1576223 = 2364335) B2364335
theorem B1051943 : Blo 698317 1051943 := bstep (se 1 (by rfl) ⟨788957, by rfl⟩ : syracuseStep 1051943 = 1577915) B1577915
theorem B789799 : Blo 698317 789799 := bstep (se 1 (by rfl) ⟨592349, by rfl⟩ : syracuseStep 789799 = 1184699) B1184699
theorem B888175 : Blo 698317 888175 := bstep (se 1 (by rfl) ⟨666131, by rfl⟩ : syracuseStep 888175 = 1332263) B1332263
theorem B789871 : Blo 698317 789871 := bstep (se 1 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 789871 = 1184807) B1184807
theorem B1183099 : Blo 698317 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B1052027 : Blo 698317 1052027 := bstep (se 1 (by rfl) ⟨789020, by rfl⟩ : syracuseStep 1052027 = 1578041) B1578041
theorem B2362823 : Blo 698317 2362823 := bstep (se 1 (by rfl) ⟨1772117, by rfl⟩ : syracuseStep 2362823 = 3544235) B3544235
theorem B1772999 : Blo 698317 1772999 := bstep (se 1 (by rfl) ⟨1329749, by rfl⟩ : syracuseStep 1772999 = 2659499) B2659499
theorem B1773049 : Blo 698317 1773049 := bstep (se 2 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 1773049 = 1329787) B1329787
theorem B1052153 : Blo 698317 1052153 := bstep (se 2 (by rfl) ⟨394557, by rfl⟩ : syracuseStep 1052153 = 789115) B789115
theorem B790087 : Blo 698317 790087 := bstep (se 1 (by rfl) ⟨592565, by rfl⟩ : syracuseStep 790087 = 1185131) B1185131
theorem B2657873 : Blo 698317 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B1052255 : Blo 698317 1052255 := bstep (se 1 (by rfl) ⟨789191, by rfl⟩ : syracuseStep 1052255 = 1578383) B1578383
theorem B2658055 : Blo 698317 2658055 := bstep (se 1 (by rfl) ⟨1993541, by rfl⟩ : syracuseStep 2658055 = 3987083) B3987083
theorem B2363147 : Blo 698317 2363147 := bstep (se 1 (by rfl) ⟨1772360, by rfl⟩ : syracuseStep 2363147 = 3544721) B3544721
theorem B1773353 : Blo 698317 1773353 := bstep (se 2 (by rfl) ⟨665007, by rfl⟩ : syracuseStep 1773353 = 1330015) B1330015
theorem B1576745 : Blo 698317 1576745 := bstep (se 2 (by rfl) ⟨591279, by rfl⟩ : syracuseStep 1576745 = 1182559) B1182559
theorem B7966511 : Blo 698317 7966511 := bstep (se 1 (by rfl) ⟨5974883, by rfl⟩ : syracuseStep 7966511 = 11949767) B11949767
theorem B1052471 : Blo 698317 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B2658329 : Blo 698317 2658329 := bstep (se 2 (by rfl) ⟨996873, by rfl⟩ : syracuseStep 2658329 = 1993747) B1993747
theorem B2363417 : Blo 698317 2363417 := bstep (se 2 (by rfl) ⟨886281, by rfl⟩ : syracuseStep 2363417 = 1772563) B1772563
theorem B1052777 : Blo 698317 1052777 := bstep (se 2 (by rfl) ⟨394791, by rfl⟩ : syracuseStep 1052777 = 789583) B789583
theorem B1773697 : Blo 698317 1773697 := bstep (se 2 (by rfl) ⟨665136, by rfl⟩ : syracuseStep 1773697 = 1330273) B1330273
theorem B1053095 : Blo 698317 1053095 := bstep (se 1 (by rfl) ⟨789821, by rfl⟩ : syracuseStep 1053095 = 1579643) B1579643
theorem B1053179 : Blo 698317 1053179 := bstep (se 1 (by rfl) ⟨789884, by rfl⟩ : syracuseStep 1053179 = 1579769) B1579769
theorem B5673523 : Blo 698317 5673523 := bstep (se 1 (by rfl) ⟨4255142, by rfl⟩ : syracuseStep 5673523 = 8510285) B8510285
theorem B4493875 : Blo 698317 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B1708607 : Blo 698317 1708607 := bstep (se 1 (by rfl) ⟨1281455, by rfl⟩ : syracuseStep 1708607 = 2562911) B2562911
theorem B1053305 : Blo 698317 1053305 := bstep (se 2 (by rfl) ⟨394989, by rfl⟩ : syracuseStep 1053305 = 789979) B789979
theorem B1053359 : Blo 698317 1053359 := bstep (se 1 (by rfl) ⟨790019, by rfl⟩ : syracuseStep 1053359 = 1580039) B1580039
theorem B1053407 : Blo 698317 1053407 := bstep (se 1 (by rfl) ⟨790055, by rfl⟩ : syracuseStep 1053407 = 1580111) B1580111
theorem B1577807 : Blo 698317 1577807 := bstep (se 1 (by rfl) ⟨1183355, by rfl⟩ : syracuseStep 1577807 = 2366711) B2366711
theorem B1184591 : Blo 698317 1184591 := bstep (se 1 (by rfl) ⟨888443, by rfl⟩ : syracuseStep 1184591 = 1776887) B1776887
theorem B1774507 : Blo 698317 1774507 := bstep (se 1 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 1774507 = 2661761) B2661761
theorem B1578023 : Blo 698317 1578023 := bstep (se 1 (by rfl) ⟨1183517, by rfl⟩ : syracuseStep 1578023 = 2367035) B2367035
theorem B1774811 : Blo 698317 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B1578203 : Blo 698317 1578203 := bstep (se 1 (by rfl) ⟨1183652, by rfl⟩ : syracuseStep 1578203 = 2367305) B2367305
theorem B2364659 : Blo 698317 2364659 := bstep (se 1 (by rfl) ⟨1773494, by rfl⟩ : syracuseStep 2364659 = 3546989) B3546989
theorem B2364767 : Blo 698317 2364767 := bstep (se 1 (by rfl) ⟨1773575, by rfl⟩ : syracuseStep 2364767 = 3547151) B3547151
theorem B1774943 : Blo 698317 1774943 := bstep (se 1 (by rfl) ⟨1331207, by rfl⟩ : syracuseStep 1774943 = 2662415) B2662415
theorem B1381769 : Blo 698317 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B1578401 : Blo 698317 1578401 := bstep (se 2 (by rfl) ⟨591900, by rfl⟩ : syracuseStep 1578401 = 1183801) B1183801
theorem B14358059 : Blo 698317 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B12785339 : Blo 698317 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B2660303 : Blo 698317 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B1578959 : Blo 698317 1578959 := bstep (se 1 (by rfl) ⟨1184219, by rfl⟩ : syracuseStep 1578959 = 2368439) B2368439
theorem B1775641 : Blo 698317 1775641 := bstep (se 2 (by rfl) ⟨665865, by rfl⟩ : syracuseStep 1775641 = 1331731) B1331731
theorem B5969963 : Blo 698317 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B2988161 : Blo 698317 2988161 := bstep (se 2 (by rfl) ⟨1120560, by rfl⟩ : syracuseStep 2988161 = 2241121) B2241121
theorem B3545369 : Blo 698317 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B1775945 : Blo 698317 1775945 := bstep (se 2 (by rfl) ⟨665979, by rfl⟩ : syracuseStep 1775945 = 1331959) B1331959
theorem B1579337 : Blo 698317 1579337 := bstep (se 2 (by rfl) ⟨592251, by rfl⟩ : syracuseStep 1579337 = 1184503) B1184503
theorem B1579355 : Blo 698317 1579355 := bstep (se 1 (by rfl) ⟨1184516, by rfl⟩ : syracuseStep 1579355 = 2369033) B2369033
theorem B2660971 : Blo 698317 2660971 := bstep (se 1 (by rfl) ⟨1995728, by rfl⟩ : syracuseStep 2660971 = 3991457) B3991457
theorem B10361519 : Blo 698317 10361519 := bstep (se 1 (by rfl) ⟨7771139, by rfl⟩ : syracuseStep 10361519 = 15542279) B15542279
theorem B5053303 : Blo 698317 5053303 := bstep (se 1 (by rfl) ⟨3789977, by rfl⟩ : syracuseStep 5053303 = 7579955) B7579955
theorem B2661245 : Blo 698317 2661245 := bstep (se 3 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 2661245 = 997967) B997967
theorem B2366333 : Blo 698317 2366333 := bstep (se 3 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 2366333 = 887375) B887375
theorem B2661275 : Blo 698317 2661275 := bstep (se 1 (by rfl) ⟨1995956, by rfl⟩ : syracuseStep 2661275 = 3991913) B3991913
theorem B1579931 : Blo 698317 1579931 := bstep (se 1 (by rfl) ⟨1184948, by rfl⟩ : syracuseStep 1579931 = 2369897) B2369897
theorem B3414971 : Blo 698317 3414971 := bstep (se 1 (by rfl) ⟨2561228, by rfl⟩ : syracuseStep 3414971 = 5122457) B5122457
theorem B1580129 : Blo 698317 1580129 := bstep (se 2 (by rfl) ⟨592548, by rfl⟩ : syracuseStep 1580129 = 1185097) B1185097
theorem B2366603 : Blo 698317 2366603 := bstep (se 1 (by rfl) ⟨1774952, by rfl⟩ : syracuseStep 2366603 = 3549905) B3549905
theorem B1678535 : Blo 698317 1678535 := bstep (se 1 (by rfl) ⟨1258901, by rfl⟩ : syracuseStep 1678535 = 2517803) B2517803
theorem B3775841 : Blo 698317 3775841 := bstep (se 2 (by rfl) ⟨1415940, by rfl⟩ : syracuseStep 3775841 = 2831881) B2831881
theorem B2989561 : Blo 698317 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B23076427 : Blo 698317 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B5971603 : Blo 698317 5971603 := bstep (se 1 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 5971603 = 8957405) B8957405
theorem B2989835 : Blo 698317 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B1679707 : Blo 698317 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B1679783 : Blo 698317 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B5054977 : Blo 698317 5054977 := bstep (se 2 (by rfl) ⟨1895616, by rfl⟩ : syracuseStep 5054977 = 3791233) B3791233
theorem B2368223 : Blo 698317 2368223 := bstep (se 1 (by rfl) ⟨1776167, by rfl⟩ : syracuseStep 2368223 = 3552335) B3552335
theorem B3548123 : Blo 698317 3548123 := bstep (se 1 (by rfl) ⟨2661092, by rfl⟩ : syracuseStep 3548123 = 5322185) B5322185
theorem B2663387 : Blo 698317 2663387 := bstep (se 1 (by rfl) ⟨1997540, by rfl⟩ : syracuseStep 2663387 = 3995081) B3995081
theorem B3548285 : Blo 698317 3548285 := bstep (se 3 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 3548285 = 1330607) B1330607
theorem B2368655 : Blo 698317 2368655 := bstep (se 1 (by rfl) ⟨1776491, by rfl⟩ : syracuseStep 2368655 = 3552983) B3552983
theorem B13673843 : Blo 698317 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B3548609 : Blo 698317 3548609 := bstep (se 2 (by rfl) ⟨1330728, by rfl⟩ : syracuseStep 3548609 = 2661457) B2661457
theorem B2991953 : Blo 698317 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B3188585 : Blo 698317 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B698319 : Blo 698317 698319 := bstep (se 1 (by rfl) ⟨523739, by rfl⟩ : syracuseStep 698319 = 1047479) B1047479
theorem B698343 : Blo 698317 698343 := bstep (se 1 (by rfl) ⟨523757, by rfl⟩ : syracuseStep 698343 = 1047515) B1047515
theorem B2369789 : Blo 698317 2369789 := bstep (se 3 (by rfl) ⟨444335, by rfl⟩ : syracuseStep 2369789 = 888671) B888671
theorem B698655 : Blo 698317 698655 := bstep (se 1 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 698655 = 1047983) B1047983
theorem B14035235 : Blo 698317 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B698715 : Blo 698317 698715 := bstep (se 1 (by rfl) ⟨524036, by rfl⟩ : syracuseStep 698715 = 1048073) B1048073
theorem B1124699 : Blo 698317 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B698735 : Blo 698317 698735 := bstep (se 1 (by rfl) ⟨524051, by rfl⟩ : syracuseStep 698735 = 1048103) B1048103
theorem B698791 : Blo 698317 698791 := bstep (se 1 (by rfl) ⟨524093, by rfl⟩ : syracuseStep 698791 = 1048187) B1048187
theorem B698875 : Blo 698317 698875 := bstep (se 1 (by rfl) ⟨524156, by rfl⟩ : syracuseStep 698875 = 1048313) B1048313
theorem B698943 : Blo 698317 698943 := bstep (se 1 (by rfl) ⟨524207, by rfl⟩ : syracuseStep 698943 = 1048415) B1048415
theorem B698951 : Blo 698317 698951 := bstep (se 1 (by rfl) ⟨524213, by rfl⟩ : syracuseStep 698951 = 1048427) B1048427
theorem B699103 : Blo 698317 699103 := bstep (se 1 (by rfl) ⟨524327, by rfl⟩ : syracuseStep 699103 = 1048655) B1048655
theorem B699183 : Blo 698317 699183 := bstep (se 1 (by rfl) ⟨524387, by rfl⟩ : syracuseStep 699183 = 1048775) B1048775
theorem B699291 : Blo 698317 699291 := bstep (se 1 (by rfl) ⟨524468, by rfl⟩ : syracuseStep 699291 = 1048937) B1048937
theorem B699343 : Blo 698317 699343 := bstep (se 1 (by rfl) ⟨524507, by rfl⟩ : syracuseStep 699343 = 1049015) B1049015
theorem B6728669 : Blo 698317 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B699367 : Blo 698317 699367 := bstep (se 1 (by rfl) ⟨524525, by rfl⟩ : syracuseStep 699367 = 1049051) B1049051
theorem B3845107 : Blo 698317 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B699679 : Blo 698317 699679 := bstep (se 1 (by rfl) ⟨524759, by rfl⟩ : syracuseStep 699679 = 1049519) B1049519
theorem B699739 : Blo 698317 699739 := bstep (se 1 (by rfl) ⟨524804, by rfl⟩ : syracuseStep 699739 = 1049609) B1049609
theorem B699759 : Blo 698317 699759 := bstep (se 1 (by rfl) ⟨524819, by rfl⟩ : syracuseStep 699759 = 1049639) B1049639
theorem B699815 : Blo 698317 699815 := bstep (se 1 (by rfl) ⟨524861, by rfl⟩ : syracuseStep 699815 = 1049723) B1049723
theorem B699899 : Blo 698317 699899 := bstep (se 1 (by rfl) ⟨524924, by rfl⟩ : syracuseStep 699899 = 1049849) B1049849
theorem B699967 : Blo 698317 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B699975 : Blo 698317 699975 := bstep (se 1 (by rfl) ⟨524981, by rfl⟩ : syracuseStep 699975 = 1049963) B1049963
theorem B2698913 : Blo 698317 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B700127 : Blo 698317 700127 := bstep (se 1 (by rfl) ⟨525095, by rfl⟩ : syracuseStep 700127 = 1050191) B1050191
theorem B995051 : Blo 698317 995051 := bstep (se 1 (by rfl) ⟨746288, by rfl⟩ : syracuseStep 995051 = 1492577) B1492577
theorem B700207 : Blo 698317 700207 := bstep (se 1 (by rfl) ⟨525155, by rfl⟩ : syracuseStep 700207 = 1050311) B1050311
theorem B3419977 : Blo 698317 3419977 := bstep (se 2 (by rfl) ⟨1282491, by rfl⟩ : syracuseStep 3419977 = 2564983) B2564983
theorem B700315 : Blo 698317 700315 := bstep (se 1 (by rfl) ⟨525236, by rfl⟩ : syracuseStep 700315 = 1050473) B1050473
theorem B700367 : Blo 698317 700367 := bstep (se 1 (by rfl) ⟨525275, by rfl⟩ : syracuseStep 700367 = 1050551) B1050551
theorem B896999 : Blo 698317 896999 := bstep (se 1 (by rfl) ⟨672749, by rfl⟩ : syracuseStep 896999 = 1345499) B1345499
theorem B700391 : Blo 698317 700391 := bstep (se 1 (by rfl) ⟨525293, by rfl⟩ : syracuseStep 700391 = 1050587) B1050587
theorem B76591169 : Blo 698317 76591169 := bstep (se 2 (by rfl) ⟨28721688, by rfl⟩ : syracuseStep 76591169 = 57443377) B57443377
theorem B700703 : Blo 698317 700703 := bstep (se 1 (by rfl) ⟨525527, by rfl⟩ : syracuseStep 700703 = 1051055) B1051055
theorem B700763 : Blo 698317 700763 := bstep (se 1 (by rfl) ⟨525572, by rfl⟩ : syracuseStep 700763 = 1051145) B1051145
theorem B700783 : Blo 698317 700783 := bstep (se 1 (by rfl) ⟨525587, by rfl⟩ : syracuseStep 700783 = 1051175) B1051175
theorem B700839 : Blo 698317 700839 := bstep (se 1 (by rfl) ⟨525629, by rfl⟩ : syracuseStep 700839 = 1051259) B1051259
theorem B15151535 : Blo 698317 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B700923 : Blo 698317 700923 := bstep (se 1 (by rfl) ⟨525692, by rfl⟩ : syracuseStep 700923 = 1051385) B1051385
theorem B700991 : Blo 698317 700991 := bstep (se 1 (by rfl) ⟨525743, by rfl⟩ : syracuseStep 700991 = 1051487) B1051487
theorem B799303 : Blo 698317 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B700999 : Blo 698317 700999 := bstep (se 1 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 700999 = 1051499) B1051499
theorem B701151 : Blo 698317 701151 := bstep (se 1 (by rfl) ⟨525863, by rfl⟩ : syracuseStep 701151 = 1051727) B1051727
theorem B1684243 : Blo 698317 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B701231 : Blo 698317 701231 := bstep (se 1 (by rfl) ⟨525923, by rfl⟩ : syracuseStep 701231 = 1051847) B1051847
theorem B701339 : Blo 698317 701339 := bstep (se 1 (by rfl) ⟨526004, by rfl⟩ : syracuseStep 701339 = 1052009) B1052009
theorem B701391 : Blo 698317 701391 := bstep (se 1 (by rfl) ⟨526043, by rfl⟩ : syracuseStep 701391 = 1052087) B1052087
theorem B701415 : Blo 698317 701415 := bstep (se 1 (by rfl) ⟨526061, by rfl⟩ : syracuseStep 701415 = 1052123) B1052123
theorem B5387411 : Blo 698317 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B3781847 : Blo 698317 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B701727 : Blo 698317 701727 := bstep (se 1 (by rfl) ⟨526295, by rfl⟩ : syracuseStep 701727 = 1052591) B1052591
theorem B701787 : Blo 698317 701787 := bstep (se 1 (by rfl) ⟨526340, by rfl⟩ : syracuseStep 701787 = 1052681) B1052681
theorem B701807 : Blo 698317 701807 := bstep (se 1 (by rfl) ⟨526355, by rfl⟩ : syracuseStep 701807 = 1052711) B1052711
theorem B701863 : Blo 698317 701863 := bstep (se 1 (by rfl) ⟨526397, by rfl⟩ : syracuseStep 701863 = 1052795) B1052795
theorem B701947 : Blo 698317 701947 := bstep (se 1 (by rfl) ⟨526460, by rfl⟩ : syracuseStep 701947 = 1052921) B1052921
theorem B702015 : Blo 698317 702015 := bstep (se 1 (by rfl) ⟨526511, by rfl⟩ : syracuseStep 702015 = 1053023) B1053023
theorem B702023 : Blo 698317 702023 := bstep (se 1 (by rfl) ⟨526517, by rfl⟩ : syracuseStep 702023 = 1053035) B1053035
theorem B702175 : Blo 698317 702175 := bstep (se 1 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 702175 = 1053263) B1053263
theorem B702255 : Blo 698317 702255 := bstep (se 1 (by rfl) ⟨526691, by rfl⟩ : syracuseStep 702255 = 1053383) B1053383
theorem B8960381 : Blo 698317 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B1686089 : Blo 698317 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B14334895 : Blo 698317 14334895 := bstep (se 1 (by rfl) ⟨10751171, by rfl⟩ : syracuseStep 14334895 = 21502343) B21502343
theorem B3357683 : Blo 698317 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B1327585 : Blo 698317 1327585 := bstep (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) B995689
theorem B1491527 : Blo 698317 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B3785287 : Blo 698317 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B13681325 : Blo 698317 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B13452101 : Blo 698317 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B5129153 : Blo 698317 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B16172045 : Blo 698317 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B3786173 : Blo 698317 3786173 := bstep (se 3 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 3786173 = 1419815) B1419815
theorem B1328633 : Blo 698317 1328633 := bstep (se 2 (by rfl) ⟨498237, by rfl⟩ : syracuseStep 1328633 = 996475) B996475
theorem B414566423 : Blo 698317 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B1493687 : Blo 698317 1493687 := bstep (se 1 (by rfl) ⟨1120265, by rfl⟩ : syracuseStep 1493687 = 2240531) B2240531
theorem B4475681 : Blo 698317 4475681 := bstep (se 2 (by rfl) ⟨1678380, by rfl⟩ : syracuseStep 4475681 = 3356761) B3356761
theorem B12798769 : Blo 698317 12798769 := bstep (se 2 (by rfl) ⟨4799538, by rfl⟩ : syracuseStep 12798769 = 9599077) B9599077
theorem B1330091 : Blo 698317 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B1494055 : Blo 698317 1494055 := bstep (se 1 (by rfl) ⟨1120541, by rfl⟩ : syracuseStep 1494055 = 2241083) B2241083
theorem B1330319 : Blo 698317 1330319 := bstep (se 1 (by rfl) ⟨997739, by rfl⟩ : syracuseStep 1330319 = 1995479) B1995479
theorem B4476221 : Blo 698317 4476221 := bstep (se 3 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 4476221 = 1678583) B1678583
theorem B1822139 : Blo 698317 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B24235463 : Blo 698317 24235463 := bstep (se 1 (by rfl) ⟨18176597, by rfl⟩ : syracuseStep 24235463 = 36353195) B36353195
theorem B11980385 : Blo 698317 11980385 := bstep (se 2 (by rfl) ⟨4492644, by rfl⟩ : syracuseStep 11980385 = 8985289) B8985289
theorem B807727 : Blo 698317 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B3789787 : Blo 698317 3789787 := bstep (se 1 (by rfl) ⟨2842340, by rfl⟩ : syracuseStep 3789787 = 5684681) B5684681
theorem B51106909 : Blo 698317 51106909 := bstep (se 3 (by rfl) ⟨9582545, by rfl⟩ : syracuseStep 51106909 = 19165091) B19165091
theorem B7558505 : Blo 698317 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B1594811 : Blo 698317 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B1889735 : Blo 698317 1889735 := bstep (se 1 (by rfl) ⟨1417301, by rfl⟩ : syracuseStep 1889735 = 2834603) B2834603
theorem B16176647 : Blo 698317 16176647 := bstep (se 1 (by rfl) ⟨12132485, by rfl⟩ : syracuseStep 16176647 = 24264971) B24264971
theorem B1889887 : Blo 698317 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B3364487 : Blo 698317 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B2021021 : Blo 698317 2021021 := bstep (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) B757883
theorem B1595177 : Blo 698317 1595177 := bstep (se 2 (by rfl) ⟨598191, by rfl⟩ : syracuseStep 1595177 = 1196383) B1196383
theorem B1988975 : Blo 698317 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B1989031 : Blo 698317 1989031 := bstep (se 1 (by rfl) ⟨1491773, by rfl⟩ : syracuseStep 1989031 = 2983547) B2983547
theorem B5691977 : Blo 698317 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B3038077 : Blo 698317 3038077 := bstep (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) B1139279
theorem B1498027 : Blo 698317 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B13491467 : Blo 698317 13491467 := bstep (se 1 (by rfl) ⟨10118600, by rfl⟩ : syracuseStep 13491467 = 20237201) B20237201
theorem B1498505 : Blo 698317 1498505 := bstep (se 2 (by rfl) ⟨561939, by rfl⟩ : syracuseStep 1498505 = 1123879) B1123879
theorem B1499087 : Blo 698317 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B3793591 : Blo 698317 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B6808465 : Blo 698317 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B7693555 : Blo 698317 7693555 := bstep (se 1 (by rfl) ⟨5770166, by rfl⟩ : syracuseStep 7693555 = 11540333) B11540333
theorem B7956305 : Blo 698317 7956305 := bstep (se 2 (by rfl) ⟨2983614, by rfl⟩ : syracuseStep 7956305 = 5967229) B5967229
theorem B2844497 : Blo 698317 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B27223897 : Blo 698317 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B2844953 : Blo 698317 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B4483471 : Blo 698317 4483471 := bstep (se 1 (by rfl) ⟨3362603, by rfl⟩ : syracuseStep 4483471 = 6725207) B6725207
theorem B3238463 : Blo 698317 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B7989839 : Blo 698317 7989839 := bstep (se 1 (by rfl) ⟨5992379, by rfl⟩ : syracuseStep 7989839 = 11984759) B11984759
theorem B13495157 : Blo 698317 13495157 := bstep (se 5 (by rfl) ⟨632585, by rfl⟩ : syracuseStep 13495157 = 1265171) B1265171
theorem B3370099 : Blo 698317 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B945371 : Blo 698317 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B4255163 : Blo 698317 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B3993097 : Blo 698317 3993097 := bstep (se 2 (by rfl) ⟨1497411, by rfl⟩ : syracuseStep 3993097 = 2994823) B2994823
theorem B5664467 : Blo 698317 5664467 := bstep (se 1 (by rfl) ⟨4248350, by rfl⟩ : syracuseStep 5664467 = 8496701) B8496701
theorem B2879293 : Blo 698317 2879293 := bstep (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) B1079735
theorem B26570753 : Blo 698317 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B7991297 : Blo 698317 7991297 := bstep (se 2 (by rfl) ⟨2996736, by rfl⟩ : syracuseStep 7991297 = 5993473) B5993473
theorem B946409 : Blo 698317 946409 := bstep (se 2 (by rfl) ⟨354903, by rfl⟩ : syracuseStep 946409 = 709807) B709807
theorem B2519387 : Blo 698317 2519387 := bstep (se 1 (by rfl) ⟨1889540, by rfl⟩ : syracuseStep 2519387 = 3779081) B3779081
theorem B3371483 : Blo 698317 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B3830689 : Blo 698317 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B3535811 : Blo 698317 3535811 := bstep (se 1 (by rfl) ⟨2651858, by rfl⟩ : syracuseStep 3535811 = 5303717) B5303717
theorem B13497617 : Blo 698317 13497617 := bstep (se 2 (by rfl) ⟨5061606, by rfl⟩ : syracuseStep 13497617 = 10123213) B10123213
theorem B5043617 : Blo 698317 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B2652527 : Blo 698317 2652527 := bstep (se 1 (by rfl) ⟨1989395, by rfl⟩ : syracuseStep 2652527 = 3978791) B3978791
theorem B1571255 : Blo 698317 1571255 := bstep (se 1 (by rfl) ⟨1178441, by rfl⟩ : syracuseStep 1571255 = 2356883) B2356883
theorem B2128447 : Blo 698317 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B1571399 : Blo 698317 1571399 := bstep (se 1 (by rfl) ⟨1178549, by rfl⟩ : syracuseStep 1571399 = 2357099) B2357099
theorem B1768007 : Blo 698317 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B1571435 : Blo 698317 1571435 := bstep (se 1 (by rfl) ⟨1178576, by rfl⟩ : syracuseStep 1571435 = 2357153) B2357153
theorem B20183687 : Blo 698317 20183687 := bstep (se 1 (by rfl) ⟨15137765, by rfl⟩ : syracuseStep 20183687 = 30275531) B30275531
theorem B1997723 : Blo 698317 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B1047527 : Blo 698317 1047527 := bstep (se 1 (by rfl) ⟨785645, by rfl⟩ : syracuseStep 1047527 = 1571291) B1571291
theorem B1571831 : Blo 698317 1571831 := bstep (se 1 (by rfl) ⟨1178873, by rfl⟩ : syracuseStep 1571831 = 2357747) B2357747
theorem B2358395 : Blo 698317 2358395 := bstep (se 1 (by rfl) ⟨1768796, by rfl⟩ : syracuseStep 2358395 = 3537593) B3537593
theorem B13499621 : Blo 698317 13499621 := bstep (se 4 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 13499621 = 2531179) B2531179
theorem B1047785 : Blo 698317 1047785 := bstep (se 2 (by rfl) ⟨392919, by rfl⟩ : syracuseStep 1047785 = 785839) B785839
theorem B785695 : Blo 698317 785695 := bstep (se 1 (by rfl) ⟨589271, by rfl⟩ : syracuseStep 785695 = 1178543) B1178543
theorem B1047839 : Blo 698317 1047839 := bstep (se 1 (by rfl) ⟨785879, by rfl⟩ : syracuseStep 1047839 = 1571759) B1571759
theorem B1572191 : Blo 698317 1572191 := bstep (se 1 (by rfl) ⟨1179143, by rfl⟩ : syracuseStep 1572191 = 2358287) B2358287
theorem B2358665 : Blo 698317 2358665 := bstep (se 2 (by rfl) ⟨884499, by rfl⟩ : syracuseStep 2358665 = 1768999) B1768999
theorem B884135 : Blo 698317 884135 := bstep (se 1 (by rfl) ⟨663101, by rfl⟩ : syracuseStep 884135 = 1326203) B1326203
theorem B1048007 : Blo 698317 1048007 := bstep (se 1 (by rfl) ⟨786005, by rfl⟩ : syracuseStep 1048007 = 1572011) B1572011
theorem B785983 : Blo 698317 785983 := bstep (se 1 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 785983 = 1178975) B1178975
theorem B884287 : Blo 698317 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B884459 : Blo 698317 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B1572587 : Blo 698317 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B1048361 : Blo 698317 1048361 := bstep (se 2 (by rfl) ⟨393135, by rfl⟩ : syracuseStep 1048361 = 786271) B786271
theorem B1048367 : Blo 698317 1048367 := bstep (se 1 (by rfl) ⟨786275, by rfl⟩ : syracuseStep 1048367 = 1572551) B1572551
theorem B1769273 : Blo 698317 1769273 := bstep (se 2 (by rfl) ⟨663477, by rfl⟩ : syracuseStep 1769273 = 1326955) B1326955
theorem B2359097 : Blo 698317 2359097 := bstep (se 2 (by rfl) ⟨884661, by rfl⟩ : syracuseStep 2359097 = 1769323) B1769323
theorem B1572713 : Blo 698317 1572713 := bstep (se 2 (by rfl) ⟨589767, by rfl⟩ : syracuseStep 1572713 = 1179535) B1179535
theorem B7995671 : Blo 698317 7995671 := bstep (se 1 (by rfl) ⟨5996753, by rfl⟩ : syracuseStep 7995671 = 11993507) B11993507
theorem B2359583 : Blo 698317 2359583 := bstep (se 1 (by rfl) ⟨1769687, by rfl⟩ : syracuseStep 2359583 = 3539375) B3539375
theorem B1769759 : Blo 698317 1769759 := bstep (se 1 (by rfl) ⟨1327319, by rfl⟩ : syracuseStep 1769759 = 2654639) B2654639
theorem B1573217 : Blo 698317 1573217 := bstep (se 2 (by rfl) ⟨589956, by rfl⟩ : syracuseStep 1573217 = 1179913) B1179913
theorem B1573307 : Blo 698317 1573307 := bstep (se 1 (by rfl) ⟨1179980, by rfl⟩ : syracuseStep 1573307 = 2359961) B2359961
theorem B1049039 : Blo 698317 1049039 := bstep (se 1 (by rfl) ⟨786779, by rfl⟩ : syracuseStep 1049039 = 1573559) B1573559
theorem B1049081 : Blo 698317 1049081 := bstep (se 2 (by rfl) ⟨393405, by rfl⟩ : syracuseStep 1049081 = 786811) B786811
theorem B1049183 : Blo 698317 1049183 := bstep (se 1 (by rfl) ⟨786887, by rfl⟩ : syracuseStep 1049183 = 1573775) B1573775
theorem B2523757 : Blo 698317 2523757 := bstep (se 3 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 2523757 = 946409) B946409
theorem B1770113 : Blo 698317 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B10781363 : Blo 698317 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B5047049 : Blo 698317 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B2360231 : Blo 698317 2360231 := bstep (se 1 (by rfl) ⟨1770173, by rfl⟩ : syracuseStep 2360231 = 3540347) B3540347
theorem B1770407 : Blo 698317 1770407 := bstep (se 1 (by rfl) ⟨1327805, by rfl⟩ : syracuseStep 1770407 = 2655611) B2655611
theorem B2524115 : Blo 698317 2524115 := bstep (se 1 (by rfl) ⟨1893086, by rfl⟩ : syracuseStep 2524115 = 3786173) B3786173
theorem B885755 : Blo 698317 885755 := bstep (se 1 (by rfl) ⟨664316, by rfl⟩ : syracuseStep 885755 = 1328633) B1328633
theorem B1049663 : Blo 698317 1049663 := bstep (se 1 (by rfl) ⟨787247, by rfl⟩ : syracuseStep 1049663 = 1574495) B1574495
theorem B1180777 : Blo 698317 1180777 := bstep (se 2 (by rfl) ⟨442791, by rfl⟩ : syracuseStep 1180777 = 885583) B885583
theorem B1049705 : Blo 698317 1049705 := bstep (se 2 (by rfl) ⟨393639, by rfl⟩ : syracuseStep 1049705 = 787279) B787279
theorem B9077953 : Blo 698317 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B1049807 : Blo 698317 1049807 := bstep (se 1 (by rfl) ⟨787355, by rfl⟩ : syracuseStep 1049807 = 1574711) B1574711
theorem B1050011 : Blo 698317 1050011 := bstep (se 1 (by rfl) ⟨787508, by rfl⟩ : syracuseStep 1050011 = 1575017) B1575017
theorem B1770923 : Blo 698317 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B1574315 : Blo 698317 1574315 := bstep (se 1 (by rfl) ⟨1180736, by rfl⟩ : syracuseStep 1574315 = 2361473) B2361473
theorem B2360825 : Blo 698317 2360825 := bstep (se 2 (by rfl) ⟨885309, by rfl⟩ : syracuseStep 2360825 = 1770619) B1770619
theorem B1050233 : Blo 698317 1050233 := bstep (se 2 (by rfl) ⟨393837, by rfl⟩ : syracuseStep 1050233 = 787675) B787675
theorem B10258073 : Blo 698317 10258073 := bstep (se 2 (by rfl) ⟨3846777, by rfl⟩ : syracuseStep 10258073 = 7693555) B7693555
theorem B1574567 : Blo 698317 1574567 := bstep (se 1 (by rfl) ⟨1180925, by rfl⟩ : syracuseStep 1574567 = 2361851) B2361851
theorem B1181351 : Blo 698317 1181351 := bstep (se 1 (by rfl) ⟨886013, by rfl⟩ : syracuseStep 1181351 = 1772027) B1772027
theorem B1050335 : Blo 698317 1050335 := bstep (se 1 (by rfl) ⟨787751, by rfl⟩ : syracuseStep 1050335 = 1575503) B1575503
theorem B3999455 : Blo 698317 3999455 := bstep (se 1 (by rfl) ⟨2999591, by rfl⟩ : syracuseStep 3999455 = 5999183) B5999183
theorem B2361095 : Blo 698317 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B2361149 : Blo 698317 2361149 := bstep (se 3 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 2361149 = 885431) B885431
theorem B1050431 : Blo 698317 1050431 := bstep (se 1 (by rfl) ⟨787823, by rfl⟩ : syracuseStep 1050431 = 1575647) B1575647
theorem B788287 : Blo 698317 788287 := bstep (se 1 (by rfl) ⟨591215, by rfl⟩ : syracuseStep 788287 = 1182431) B1182431
theorem B2983787 : Blo 698317 2983787 := bstep (se 1 (by rfl) ⟨2237840, by rfl⟩ : syracuseStep 2983787 = 4475681) B4475681
theorem B1574855 : Blo 698317 1574855 := bstep (se 1 (by rfl) ⟨1181141, by rfl⟩ : syracuseStep 1574855 = 2362283) B2362283
theorem B886727 : Blo 698317 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B1050599 : Blo 698317 1050599 := bstep (se 1 (by rfl) ⟨787949, by rfl⟩ : syracuseStep 1050599 = 1575899) B1575899
theorem B1050617 : Blo 698317 1050617 := bstep (se 2 (by rfl) ⟨393981, by rfl⟩ : syracuseStep 1050617 = 787963) B787963
theorem B1050719 : Blo 698317 1050719 := bstep (se 1 (by rfl) ⟨788039, by rfl⟩ : syracuseStep 1050719 = 1576079) B1576079
theorem B886879 : Blo 698317 886879 := bstep (se 1 (by rfl) ⟨665159, by rfl⟩ : syracuseStep 886879 = 1330319) B1330319
theorem B788575 : Blo 698317 788575 := bstep (se 1 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 788575 = 1182863) B1182863
theorem B1050779 : Blo 698317 1050779 := bstep (se 1 (by rfl) ⟨788084, by rfl⟩ : syracuseStep 1050779 = 1576169) B1576169
theorem B1050815 : Blo 698317 1050815 := bstep (se 1 (by rfl) ⟨788111, by rfl⟩ : syracuseStep 1050815 = 1576223) B1576223
theorem B2984147 : Blo 698317 2984147 := bstep (se 1 (by rfl) ⟨2238110, by rfl⟩ : syracuseStep 2984147 = 4476221) B4476221
theorem B1050857 : Blo 698317 1050857 := bstep (se 2 (by rfl) ⟨394071, by rfl⟩ : syracuseStep 1050857 = 788143) B788143
theorem B1575161 : Blo 698317 1575161 := bstep (se 2 (by rfl) ⟨590685, by rfl⟩ : syracuseStep 1575161 = 1181371) B1181371
theorem B1214759 : Blo 698317 1214759 := bstep (se 1 (by rfl) ⟨911069, by rfl⟩ : syracuseStep 1214759 = 1822139) B1822139
theorem B1575215 : Blo 698317 1575215 := bstep (se 1 (by rfl) ⟨1181411, by rfl⟩ : syracuseStep 1575215 = 2362823) B2362823
theorem B1181999 : Blo 698317 1181999 := bstep (se 1 (by rfl) ⟨886499, by rfl⟩ : syracuseStep 1181999 = 1772999) B1772999
theorem B1771915 : Blo 698317 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B1575431 : Blo 698317 1575431 := bstep (se 1 (by rfl) ⟨1181573, by rfl⟩ : syracuseStep 1575431 = 2363147) B2363147
theorem B1182235 : Blo 698317 1182235 := bstep (se 1 (by rfl) ⟨886676, by rfl⟩ : syracuseStep 1182235 = 1773353) B1773353
theorem B1051163 : Blo 698317 1051163 := bstep (se 1 (by rfl) ⟨788372, by rfl⟩ : syracuseStep 1051163 = 1576745) B1576745
theorem B5311007 : Blo 698317 5311007 := bstep (se 1 (by rfl) ⟨3983255, by rfl⟩ : syracuseStep 5311007 = 7966511) B7966511
theorem B1051241 : Blo 698317 1051241 := bstep (se 2 (by rfl) ⟨394215, by rfl⟩ : syracuseStep 1051241 = 788431) B788431
theorem B1772219 : Blo 698317 1772219 := bstep (se 1 (by rfl) ⟨1329164, by rfl⟩ : syracuseStep 1772219 = 2658329) B2658329
theorem B1575611 : Blo 698317 1575611 := bstep (se 1 (by rfl) ⟨1181708, by rfl⟩ : syracuseStep 1575611 = 2363417) B2363417
theorem B1051769 : Blo 698317 1051769 := bstep (se 2 (by rfl) ⟨394413, by rfl⟩ : syracuseStep 1051769 = 788827) B788827
theorem B1051871 : Blo 698317 1051871 := bstep (se 1 (by rfl) ⟨788903, by rfl⟩ : syracuseStep 1051871 = 1577807) B1577807
theorem B789727 : Blo 698317 789727 := bstep (se 1 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 789727 = 1184591) B1184591
theorem B1051913 : Blo 698317 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B1052015 : Blo 698317 1052015 := bstep (se 1 (by rfl) ⟨789011, by rfl⟩ : syracuseStep 1052015 = 1578023) B1578023
theorem B1183207 : Blo 698317 1183207 := bstep (se 1 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 1183207 = 1774811) B1774811
theorem B1052135 : Blo 698317 1052135 := bstep (se 1 (by rfl) ⟨789101, by rfl⟩ : syracuseStep 1052135 = 1578203) B1578203
theorem B1576439 : Blo 698317 1576439 := bstep (se 1 (by rfl) ⟨1182329, by rfl⟩ : syracuseStep 1576439 = 2364659) B2364659
theorem B1576511 : Blo 698317 1576511 := bstep (se 1 (by rfl) ⟨1182383, by rfl⟩ : syracuseStep 1576511 = 2364767) B2364767
theorem B1183295 : Blo 698317 1183295 := bstep (se 1 (by rfl) ⟨887471, by rfl⟩ : syracuseStep 1183295 = 1774943) B1774943
theorem B921179 : Blo 698317 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B1052267 : Blo 698317 1052267 := bstep (se 1 (by rfl) ⟨789200, by rfl⟩ : syracuseStep 1052267 = 1578401) B1578401
theorem B10784431 : Blo 698317 10784431 := bstep (se 1 (by rfl) ⟨8088323, by rfl⟩ : syracuseStep 10784431 = 16176647) B16176647
theorem B9572039 : Blo 698317 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1052393 : Blo 698317 1052393 := bstep (se 2 (by rfl) ⟨394647, by rfl⟩ : syracuseStep 1052393 = 789295) B789295
theorem B1347347 : Blo 698317 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B8523559 : Blo 698317 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B1052537 : Blo 698317 1052537 := bstep (se 2 (by rfl) ⟨394701, by rfl⟩ : syracuseStep 1052537 = 789403) B789403
theorem B1773535 : Blo 698317 1773535 := bstep (se 1 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 1773535 = 2660303) B2660303
theorem B1052639 : Blo 698317 1052639 := bstep (se 1 (by rfl) ⟨789479, by rfl⟩ : syracuseStep 1052639 = 1578959) B1578959
theorem B4493465 : Blo 698317 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B2363579 : Blo 698317 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B1183963 : Blo 698317 1183963 := bstep (se 1 (by rfl) ⟨887972, by rfl⟩ : syracuseStep 1183963 = 1775945) B1775945
theorem B1052891 : Blo 698317 1052891 := bstep (se 1 (by rfl) ⟨789668, by rfl⟩ : syracuseStep 1052891 = 1579337) B1579337
theorem B1052903 : Blo 698317 1052903 := bstep (se 1 (by rfl) ⟨789677, by rfl⟩ : syracuseStep 1052903 = 1579355) B1579355
theorem B1053065 : Blo 698317 1053065 := bstep (se 2 (by rfl) ⟨394899, by rfl⟩ : syracuseStep 1053065 = 789799) B789799
theorem B1184233 : Blo 698317 1184233 := bstep (se 2 (by rfl) ⟨444087, by rfl⟩ : syracuseStep 1184233 = 888175) B888175
theorem B1053161 : Blo 698317 1053161 := bstep (se 2 (by rfl) ⟨394935, by rfl⟩ : syracuseStep 1053161 = 789871) B789871
theorem B1577465 : Blo 698317 1577465 := bstep (se 2 (by rfl) ⟨591549, by rfl⟩ : syracuseStep 1577465 = 1183099) B1183099
theorem B1774163 : Blo 698317 1774163 := bstep (se 1 (by rfl) ⟨1330622, by rfl⟩ : syracuseStep 1774163 = 2661245) B2661245
theorem B1577555 : Blo 698317 1577555 := bstep (se 1 (by rfl) ⟨1183166, by rfl⟩ : syracuseStep 1577555 = 2366333) B2366333
theorem B1774183 : Blo 698317 1774183 := bstep (se 1 (by rfl) ⟨1330637, by rfl⟩ : syracuseStep 1774183 = 2661275) B2661275
theorem B1053287 : Blo 698317 1053287 := bstep (se 1 (by rfl) ⟨789965, by rfl⟩ : syracuseStep 1053287 = 1579931) B1579931
theorem B2364065 : Blo 698317 2364065 := bstep (se 2 (by rfl) ⟨886524, by rfl⟩ : syracuseStep 2364065 = 1773049) B1773049
theorem B1053419 : Blo 698317 1053419 := bstep (se 1 (by rfl) ⟨790064, by rfl⟩ : syracuseStep 1053419 = 1580129) B1580129
theorem B1577735 : Blo 698317 1577735 := bstep (se 1 (by rfl) ⟨1183301, by rfl⟩ : syracuseStep 1577735 = 2366603) B2366603
theorem B1053449 : Blo 698317 1053449 := bstep (se 2 (by rfl) ⟨395043, by rfl⟩ : syracuseStep 1053449 = 790087) B790087
theorem B1119023 : Blo 698317 1119023 := bstep (se 1 (by rfl) ⟨839267, by rfl⟩ : syracuseStep 1119023 = 1678535) B1678535
theorem B3544073 : Blo 698317 3544073 := bstep (se 2 (by rfl) ⟨1329027, by rfl⟩ : syracuseStep 3544073 = 2658055) B2658055
theorem B3839057 : Blo 698317 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B4559969 : Blo 698317 4559969 := bstep (se 2 (by rfl) ⟨1709988, by rfl⟩ : syracuseStep 4559969 = 3419977) B3419977
theorem B2364929 : Blo 698317 2364929 := bstep (se 2 (by rfl) ⟨886848, by rfl⟩ : syracuseStep 2364929 = 1773697) B1773697
theorem B1578815 : Blo 698317 1578815 := bstep (se 1 (by rfl) ⟨1184111, by rfl⟩ : syracuseStep 1578815 = 2368223) B2368223
theorem B2365415 : Blo 698317 2365415 := bstep (se 1 (by rfl) ⟨1774061, by rfl⟩ : syracuseStep 2365415 = 3548123) B3548123
theorem B1775591 : Blo 698317 1775591 := bstep (se 1 (by rfl) ⟨1331693, by rfl⟩ : syracuseStep 1775591 = 2663387) B2663387
theorem B2365523 : Blo 698317 2365523 := bstep (se 1 (by rfl) ⟨1774142, by rfl⟩ : syracuseStep 2365523 = 3548285) B3548285
theorem B37427293 : Blo 698317 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B1579103 : Blo 698317 1579103 := bstep (se 1 (by rfl) ⟨1184327, by rfl⟩ : syracuseStep 1579103 = 2368655) B2368655
theorem B9115895 : Blo 698317 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B2365739 : Blo 698317 2365739 := bstep (se 1 (by rfl) ⟨1774304, by rfl⟩ : syracuseStep 2365739 = 3548609) B3548609
theorem B2366009 : Blo 698317 2366009 := bstep (se 2 (by rfl) ⟨887253, by rfl⟩ : syracuseStep 2366009 = 1774507) B1774507
theorem B5053049 : Blo 698317 5053049 := bstep (se 2 (by rfl) ⟨1894893, by rfl⟩ : syracuseStep 5053049 = 3789787) B3789787
theorem B1579859 : Blo 698317 1579859 := bstep (se 1 (by rfl) ⟨1184894, by rfl⟩ : syracuseStep 1579859 = 2369789) B2369789
theorem B3776311 : Blo 698317 3776311 := bstep (se 1 (by rfl) ⟨2832233, by rfl⟩ : syracuseStep 3776311 = 5664467) B5664467
theorem B2367521 : Blo 698317 2367521 := bstep (se 2 (by rfl) ⟨887820, by rfl⟩ : syracuseStep 2367521 = 1775641) B1775641
theorem B51060779 : Blo 698317 51060779 := bstep (se 1 (by rfl) ⟨38295584, by rfl⟩ : syracuseStep 51060779 = 76591169) B76591169
theorem B1679591 : Blo 698317 1679591 := bstep (se 1 (by rfl) ⟨1259693, by rfl⟩ : syracuseStep 1679591 = 2519387) B2519387
theorem B10101023 : Blo 698317 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B3547961 : Blo 698317 3547961 := bstep (se 2 (by rfl) ⟨1330485, by rfl⟩ : syracuseStep 3547961 = 2660971) B2660971
theorem B64627901 : Blo 698317 64627901 := bstep (se 3 (by rfl) ⟨12117731, by rfl⟩ : syracuseStep 64627901 = 24235463) B24235463
theorem B19113193 : Blo 698317 19113193 := bstep (se 2 (by rfl) ⟨7167447, by rfl⟩ : syracuseStep 19113193 = 14334895) B14334895
theorem B5973587 : Blo 698317 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B1124059 : Blo 698317 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B698351 : Blo 698317 698351 := bstep (se 1 (by rfl) ⟨523763, by rfl⟩ : syracuseStep 698351 = 1047527) B1047527
theorem B2238455 : Blo 698317 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B698523 : Blo 698317 698523 := bstep (se 1 (by rfl) ⟨523892, by rfl⟩ : syracuseStep 698523 = 1047785) B1047785
theorem B698559 : Blo 698317 698559 := bstep (se 1 (by rfl) ⟨523919, by rfl⟩ : syracuseStep 698559 = 1047839) B1047839
theorem B698671 : Blo 698317 698671 := bstep (se 1 (by rfl) ⟨524003, by rfl⟩ : syracuseStep 698671 = 1048007) B1048007
theorem B698907 : Blo 698317 698907 := bstep (se 1 (by rfl) ⟨524180, by rfl⟩ : syracuseStep 698907 = 1048361) B1048361
theorem B698911 : Blo 698317 698911 := bstep (se 1 (by rfl) ⟨524183, by rfl⟩ : syracuseStep 698911 = 1048367) B1048367
theorem B699227 : Blo 698317 699227 := bstep (se 1 (by rfl) ⟨524420, by rfl⟩ : syracuseStep 699227 = 1048841) B1048841
theorem B699295 : Blo 698317 699295 := bstep (se 1 (by rfl) ⟨524471, by rfl⟩ : syracuseStep 699295 = 1048943) B1048943
theorem B994351 : Blo 698317 994351 := bstep (se 1 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 994351 = 1491527) B1491527
theorem B699439 : Blo 698317 699439 := bstep (se 1 (by rfl) ⟨524579, by rfl⟩ : syracuseStep 699439 = 1049159) B1049159
theorem B699463 : Blo 698317 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B9120883 : Blo 698317 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B2239609 : Blo 698317 2239609 := bstep (se 2 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 2239609 = 1679707) B1679707
theorem B699615 : Blo 698317 699615 := bstep (se 1 (by rfl) ⟨524711, by rfl⟩ : syracuseStep 699615 = 1049423) B1049423
theorem B3419435 : Blo 698317 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B699879 : Blo 698317 699879 := bstep (se 1 (by rfl) ⟨524909, by rfl⟩ : syracuseStep 699879 = 1049819) B1049819
theorem B5058121 : Blo 698317 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B699995 : Blo 698317 699995 := bstep (se 1 (by rfl) ⟨524996, by rfl⟩ : syracuseStep 699995 = 1049993) B1049993
theorem B1683119 : Blo 698317 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B700231 : Blo 698317 700231 := bstep (se 1 (by rfl) ⟨525173, by rfl⟩ : syracuseStep 700231 = 1050347) B1050347
theorem B8990621 : Blo 698317 8990621 := bstep (se 3 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 8990621 = 3371483) B3371483
theorem B700383 : Blo 698317 700383 := bstep (se 1 (by rfl) ⟨525287, by rfl⟩ : syracuseStep 700383 = 1050575) B1050575
theorem B276377615 : Blo 698317 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B700647 : Blo 698317 700647 := bstep (se 1 (by rfl) ⟨525485, by rfl⟩ : syracuseStep 700647 = 1050971) B1050971
theorem B700799 : Blo 698317 700799 := bstep (se 1 (by rfl) ⟨525599, by rfl⟩ : syracuseStep 700799 = 1051199) B1051199
theorem B700879 : Blo 698317 700879 := bstep (se 1 (by rfl) ⟨525659, by rfl⟩ : syracuseStep 700879 = 1051319) B1051319
theorem B701031 : Blo 698317 701031 := bstep (se 1 (by rfl) ⟨525773, by rfl⟩ : syracuseStep 701031 = 1051547) B1051547
theorem B701295 : Blo 698317 701295 := bstep (se 1 (by rfl) ⟨525971, by rfl⟩ : syracuseStep 701295 = 1051943) B1051943
theorem B701351 : Blo 698317 701351 := bstep (se 1 (by rfl) ⟨526013, by rfl⟩ : syracuseStep 701351 = 1052027) B1052027
theorem B701435 : Blo 698317 701435 := bstep (se 1 (by rfl) ⟨526076, by rfl⟩ : syracuseStep 701435 = 1052153) B1052153
theorem B701503 : Blo 698317 701503 := bstep (se 1 (by rfl) ⟨526127, by rfl⟩ : syracuseStep 701503 = 1052255) B1052255
theorem B701647 : Blo 698317 701647 := bstep (se 1 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 701647 = 1052471) B1052471
theorem B701851 : Blo 698317 701851 := bstep (se 1 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 701851 = 1052777) B1052777
theorem B702063 : Blo 698317 702063 := bstep (se 1 (by rfl) ⟨526547, by rfl⟩ : syracuseStep 702063 = 1053095) B1053095
theorem B702119 : Blo 698317 702119 := bstep (se 1 (by rfl) ⟨526589, by rfl⟩ : syracuseStep 702119 = 1053179) B1053179
theorem B8763125 : Blo 698317 8763125 := bstep (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) B821543
theorem B702203 : Blo 698317 702203 := bstep (se 1 (by rfl) ⟨526652, by rfl⟩ : syracuseStep 702203 = 1053305) B1053305
theorem B702239 : Blo 698317 702239 := bstep (se 1 (by rfl) ⟨526679, by rfl⟩ : syracuseStep 702239 = 1053359) B1053359
theorem B702271 : Blo 698317 702271 := bstep (se 1 (by rfl) ⟨526703, by rfl⟩ : syracuseStep 702271 = 1053407) B1053407
theorem B5977961 : Blo 698317 5977961 := bstep (se 2 (by rfl) ⟨2241735, by rfl⟩ : syracuseStep 5977961 = 4483471) B4483471
theorem B1063207 : Blo 698317 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B2242991 : Blo 698317 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B1063451 : Blo 698317 1063451 := bstep (se 1 (by rfl) ⟨797588, by rfl⟩ : syracuseStep 1063451 = 1595177) B1595177
theorem B5126809 : Blo 698317 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B3979975 : Blo 698317 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B1325983 : Blo 698317 1325983 := bstep (se 1 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 1325983 = 1988975) B1988975
theorem B5324129 : Blo 698317 5324129 := bstep (se 2 (by rfl) ⟨1996548, by rfl⟩ : syracuseStep 5324129 = 3993097) B3993097
theorem B8994311 : Blo 698317 8994311 := bstep (se 1 (by rfl) ⟨6745733, by rfl⟩ : syracuseStep 8994311 = 13491467) B13491467
theorem B999391 : Blo 698317 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B1065737 : Blo 698317 1065737 := bstep (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) B799303
theorem B2999197 : Blo 698317 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B2245657 : Blo 698317 2245657 := bstep (se 2 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 2245657 = 1684243) B1684243
theorem B68142545 : Blo 698317 68142545 := bstep (se 2 (by rfl) ⟨25553454, by rfl⟩ : syracuseStep 68142545 = 51106909) B51106909
theorem B8635901 : Blo 698317 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B5326559 : Blo 698317 5326559 := bstep (se 1 (by rfl) ⟨3994919, by rfl⟩ : syracuseStep 5326559 = 7989839) B7989839
theorem B3983165 : Blo 698317 3983165 := bstep (se 3 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 3983165 = 1493687) B1493687
theorem B8996771 : Blo 698317 8996771 := bstep (se 1 (by rfl) ⟨6747578, by rfl⟩ : syracuseStep 8996771 = 13495157) B13495157
theorem B2836775 : Blo 698317 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B17713835 : Blo 698317 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B5327531 : Blo 698317 5327531 := bstep (se 1 (by rfl) ⟨3995648, by rfl⟩ : syracuseStep 5327531 = 7991297) B7991297
theorem B2837929 : Blo 698317 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B3591607 : Blo 698317 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B8998411 : Blo 698317 8998411 := bstep (se 1 (by rfl) ⟨6748808, by rfl⟩ : syracuseStep 8998411 = 13497617) B13497617
theorem B3362411 : Blo 698317 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B6737737 : Blo 698317 6737737 := bstep (se 2 (by rfl) ⟨2526651, by rfl⟩ : syracuseStep 6737737 = 5053303) B5053303
theorem B4050769 : Blo 698317 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B13455791 : Blo 698317 13455791 := bstep (se 1 (by rfl) ⟨10091843, by rfl⟩ : syracuseStep 13455791 = 20183687) B20183687
theorem B1331815 : Blo 698317 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B3986081 : Blo 698317 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B8999747 : Blo 698317 8999747 := bstep (se 1 (by rfl) ⟨6749810, by rfl⟩ : syracuseStep 8999747 = 13499621) B13499621
theorem B8968067 : Blo 698317 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B6739969 : Blo 698317 6739969 := bstep (se 2 (by rfl) ⟨2527488, by rfl⟩ : syracuseStep 6739969 = 5054977) B5054977
theorem B4479421 : Blo 698317 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B20798209 : Blo 698317 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B1989623 : Blo 698317 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B7986923 : Blo 698317 7986923 := bstep (se 1 (by rfl) ⟨5990192, by rfl⟩ : syracuseStep 7986923 = 11980385) B11980385
theorem B36298529 : Blo 698317 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B1139071 : Blo 698317 1139071 := bstep (se 1 (by rfl) ⟨854303, by rfl⟩ : syracuseStep 1139071 = 1708607) B1708607
theorem B10084925 : Blo 698317 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B5039003 : Blo 698317 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B17065025 : Blo 698317 17065025 := bstep (se 2 (by rfl) ⟨6399384, by rfl⟩ : syracuseStep 17065025 = 12798769) B12798769
theorem B5039293 : Blo 698317 5039293 := bstep (se 3 (by rfl) ⟨944867, by rfl⟩ : syracuseStep 5039293 = 1889735) B1889735
theorem B1992073 : Blo 698317 1992073 := bstep (se 2 (by rfl) ⟨747027, by rfl⟩ : syracuseStep 1992073 = 1494055) B1494055
theorem B1992107 : Blo 698317 1992107 := bstep (se 1 (by rfl) ⟨1494080, by rfl⟩ : syracuseStep 1992107 = 2988161) B2988161
theorem B3794651 : Blo 698317 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B6907679 : Blo 698317 6907679 := bstep (se 1 (by rfl) ⟨5180759, by rfl⟩ : syracuseStep 6907679 = 10361519) B10361519
theorem B2517227 : Blo 698317 2517227 := bstep (se 1 (by rfl) ⟨1887920, by rfl⟩ : syracuseStep 2517227 = 3775841) B3775841
theorem B1993223 : Blo 698317 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B7564697 : Blo 698317 7564697 := bstep (se 2 (by rfl) ⟨2836761, by rfl⟩ : syracuseStep 7564697 = 5673523) B5673523
theorem B5991833 : Blo 698317 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B1076969 : Blo 698317 1076969 := bstep (se 2 (by rfl) ⟨403863, by rfl⟩ : syracuseStep 1076969 = 807727) B807727
theorem B5107585 : Blo 698317 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B5304203 : Blo 698317 5304203 := bstep (se 1 (by rfl) ⟨3978152, by rfl⟩ : syracuseStep 5304203 = 7956305) B7956305
theorem B1994635 : Blo 698317 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B1896331 : Blo 698317 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B2125723 : Blo 698317 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B1896635 : Blo 698317 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B4485779 : Blo 698317 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B2519849 : Blo 698317 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B1799275 : Blo 698317 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B9106589 : Blo 698317 9106589 := bstep (se 3 (by rfl) ⟨1707485, by rfl⟩ : syracuseStep 9106589 = 3414971) B3414971
theorem B2652041 : Blo 698317 2652041 := bstep (se 2 (by rfl) ⟨994515, by rfl⟩ : syracuseStep 2652041 = 1989031) B1989031
theorem B2520989 : Blo 698317 2520989 := bstep (se 3 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 2520989 = 945371) B945371
theorem B2357207 : Blo 698317 2357207 := bstep (se 1 (by rfl) ⟨1767905, by rfl⟩ : syracuseStep 2357207 = 3535811) B3535811
theorem B3996013 : Blo 698317 3996013 := bstep (se 3 (by rfl) ⟨749252, by rfl⟩ : syracuseStep 3996013 = 1498505) B1498505
theorem B2357693 : Blo 698317 2357693 := bstep (se 3 (by rfl) ⟨442067, by rfl⟩ : syracuseStep 2357693 = 884135) B884135
theorem B1997369 : Blo 698317 1997369 := bstep (se 2 (by rfl) ⟨749013, by rfl⟩ : syracuseStep 1997369 = 1498027) B1498027
theorem B1768351 : Blo 698317 1768351 := bstep (se 1 (by rfl) ⟨1326263, by rfl⟩ : syracuseStep 1768351 = 2652527) B2652527
theorem B1047503 : Blo 698317 1047503 := bstep (se 1 (by rfl) ⟨785627, by rfl⟩ : syracuseStep 1047503 = 1571255) B1571255
theorem B1047593 : Blo 698317 1047593 := bstep (se 2 (by rfl) ⟨392847, by rfl⟩ : syracuseStep 1047593 = 785695) B785695
theorem B1047599 : Blo 698317 1047599 := bstep (se 1 (by rfl) ⟨785699, by rfl⟩ : syracuseStep 1047599 = 1571399) B1571399
theorem B1178671 : Blo 698317 1178671 := bstep (se 1 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 1178671 = 1768007) B1768007
theorem B1047623 : Blo 698317 1047623 := bstep (se 1 (by rfl) ⟨785717, by rfl⟩ : syracuseStep 1047623 = 1571435) B1571435
theorem B2358557 : Blo 698317 2358557 := bstep (se 3 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 2358557 = 884459) B884459
theorem B2653469 : Blo 698317 2653469 := bstep (se 3 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 2653469 = 995051) B995051
theorem B1047887 : Blo 698317 1047887 := bstep (se 1 (by rfl) ⟨785915, by rfl⟩ : syracuseStep 1047887 = 1571831) B1571831
theorem B1572263 : Blo 698317 1572263 := bstep (se 1 (by rfl) ⟨1179197, by rfl⟩ : syracuseStep 1572263 = 2358395) B2358395
theorem B1047977 : Blo 698317 1047977 := bstep (se 2 (by rfl) ⟨392991, by rfl⟩ : syracuseStep 1047977 = 785983) B785983
theorem B1179049 : Blo 698317 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B30768569 : Blo 698317 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B7962137 : Blo 698317 7962137 := bstep (se 2 (by rfl) ⟨2985801, by rfl⟩ : syracuseStep 7962137 = 5971603) B5971603
theorem B1048127 : Blo 698317 1048127 := bstep (se 1 (by rfl) ⟨786095, by rfl⟩ : syracuseStep 1048127 = 1572191) B1572191
theorem B1572443 : Blo 698317 1572443 := bstep (se 1 (by rfl) ⟨1179332, by rfl⟩ : syracuseStep 1572443 = 2358665) B2358665
theorem B9567989 : Blo 698317 9567989 := bstep (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) B896999
theorem B1048391 : Blo 698317 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B1179515 : Blo 698317 1179515 := bstep (se 1 (by rfl) ⟨884636, by rfl⟩ : syracuseStep 1179515 = 1769273) B1769273
theorem B1572731 : Blo 698317 1572731 := bstep (se 1 (by rfl) ⟨1179548, by rfl⟩ : syracuseStep 1572731 = 2359097) B2359097
theorem B1048475 : Blo 698317 1048475 := bstep (se 1 (by rfl) ⟨786356, by rfl⟩ : syracuseStep 1048475 = 1572713) B1572713
theorem B1573055 : Blo 698317 1573055 := bstep (se 1 (by rfl) ⟨1179791, by rfl⟩ : syracuseStep 1573055 = 2359583) B2359583
theorem B1179839 : Blo 698317 1179839 := bstep (se 1 (by rfl) ⟨884879, by rfl⟩ : syracuseStep 1179839 = 1769759) B1769759
theorem B1048811 : Blo 698317 1048811 := bstep (se 1 (by rfl) ⟨786608, by rfl⟩ : syracuseStep 1048811 = 1573217) B1573217
theorem B1048871 : Blo 698317 1048871 := bstep (se 1 (by rfl) ⟨786653, by rfl⟩ : syracuseStep 1048871 = 1573307) B1573307
theorem B1180075 : Blo 698317 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B1573487 : Blo 698317 1573487 := bstep (se 1 (by rfl) ⟨1180115, by rfl⟩ : syracuseStep 1573487 = 2360231) B2360231
theorem B1180271 : Blo 698317 1180271 := bstep (se 1 (by rfl) ⟨885203, by rfl⟩ : syracuseStep 1180271 = 1770407) B1770407
theorem B1180615 : Blo 698317 1180615 := bstep (se 1 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 1180615 = 1770923) B1770923
theorem B1049543 : Blo 698317 1049543 := bstep (se 1 (by rfl) ⟨787157, by rfl⟩ : syracuseStep 1049543 = 1574315) B1574315
theorem B1573883 : Blo 698317 1573883 := bstep (se 1 (by rfl) ⟨1180412, by rfl⟩ : syracuseStep 1573883 = 2360825) B2360825
theorem B1049711 : Blo 698317 1049711 := bstep (se 1 (by rfl) ⟨787283, by rfl⟩ : syracuseStep 1049711 = 1574567) B1574567
theorem B787567 : Blo 698317 787567 := bstep (se 1 (by rfl) ⟨590675, by rfl⟩ : syracuseStep 787567 = 1181351) B1181351
theorem B1574063 : Blo 698317 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B3998929 : Blo 698317 3998929 := bstep (se 2 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 3998929 = 2999197) B2999197
theorem B2655443 : Blo 698317 2655443 := bstep (se 1 (by rfl) ⟨1991582, by rfl⟩ : syracuseStep 2655443 = 3983165) B3983165
theorem B1574099 : Blo 698317 1574099 := bstep (se 1 (by rfl) ⟨1180574, by rfl⟩ : syracuseStep 1574099 = 2361149) B2361149
theorem B5997847 : Blo 698317 5997847 := bstep (se 1 (by rfl) ⟨4498385, by rfl⟩ : syracuseStep 5997847 = 8996771) B8996771
theorem B1049903 : Blo 698317 1049903 := bstep (se 1 (by rfl) ⟨787427, by rfl⟩ : syracuseStep 1049903 = 1574855) B1574855
theorem B1574369 : Blo 698317 1574369 := bstep (se 2 (by rfl) ⟨590388, by rfl⟩ : syracuseStep 1574369 = 1180777) B1180777
theorem B1050107 : Blo 698317 1050107 := bstep (se 1 (by rfl) ⟨787580, by rfl⟩ : syracuseStep 1050107 = 1575161) B1575161
theorem B1050143 : Blo 698317 1050143 := bstep (se 1 (by rfl) ⟨787607, by rfl⟩ : syracuseStep 1050143 = 1575215) B1575215
theorem B787999 : Blo 698317 787999 := bstep (se 1 (by rfl) ⟨590999, by rfl⟩ : syracuseStep 787999 = 1181999) B1181999
theorem B6719057 : Blo 698317 6719057 := bstep (se 2 (by rfl) ⟨2519646, by rfl⟩ : syracuseStep 6719057 = 5039293) B5039293
theorem B1050287 : Blo 698317 1050287 := bstep (se 1 (by rfl) ⟨787715, by rfl⟩ : syracuseStep 1050287 = 1575431) B1575431
theorem B3540671 : Blo 698317 3540671 := bstep (se 1 (by rfl) ⟨2655503, by rfl⟩ : syracuseStep 3540671 = 5311007) B5311007
theorem B1181479 : Blo 698317 1181479 := bstep (se 1 (by rfl) ⟨886109, by rfl⟩ : syracuseStep 1181479 = 1772219) B1772219
theorem B1050407 : Blo 698317 1050407 := bstep (se 1 (by rfl) ⟨787805, by rfl⟩ : syracuseStep 1050407 = 1575611) B1575611
theorem B2656097 : Blo 698317 2656097 := bstep (se 2 (by rfl) ⟨996036, by rfl⟩ : syracuseStep 2656097 = 1992073) B1992073
theorem B1050959 : Blo 698317 1050959 := bstep (se 1 (by rfl) ⟨788219, by rfl⟩ : syracuseStep 1050959 = 1576439) B1576439
theorem B1051007 : Blo 698317 1051007 := bstep (se 1 (by rfl) ⟨788255, by rfl⟩ : syracuseStep 1051007 = 1576511) B1576511
theorem B788863 : Blo 698317 788863 := bstep (se 1 (by rfl) ⟨591647, by rfl⟩ : syracuseStep 788863 = 1183295) B1183295
theorem B1051049 : Blo 698317 1051049 := bstep (se 2 (by rfl) ⟨394143, by rfl⟩ : syracuseStep 1051049 = 788287) B788287
theorem B2362013 : Blo 698317 2362013 := bstep (se 3 (by rfl) ⟨442877, by rfl⟩ : syracuseStep 2362013 = 885755) B885755
theorem B1575719 : Blo 698317 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B1182505 : Blo 698317 1182505 := bstep (se 2 (by rfl) ⟨443439, by rfl⟩ : syracuseStep 1182505 = 886879) B886879
theorem B1051433 : Blo 698317 1051433 := bstep (se 2 (by rfl) ⟨394287, by rfl⟩ : syracuseStep 1051433 = 788575) B788575
theorem B1051643 : Blo 698317 1051643 := bstep (se 1 (by rfl) ⟨788732, by rfl⟩ : syracuseStep 1051643 = 1577465) B1577465
theorem B1182775 : Blo 698317 1182775 := bstep (se 1 (by rfl) ⟨887081, by rfl⟩ : syracuseStep 1182775 = 1774163) B1774163
theorem B1051703 : Blo 698317 1051703 := bstep (se 1 (by rfl) ⟨788777, by rfl⟩ : syracuseStep 1051703 = 1577555) B1577555
theorem B2657387 : Blo 698317 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B1576043 : Blo 698317 1576043 := bstep (se 1 (by rfl) ⟨1182032, by rfl⟩ : syracuseStep 1576043 = 2364065) B2364065
theorem B1051823 : Blo 698317 1051823 := bstep (se 1 (by rfl) ⟨788867, by rfl⟩ : syracuseStep 1051823 = 1577735) B1577735
theorem B2362553 : Blo 698317 2362553 := bstep (se 2 (by rfl) ⟨885957, by rfl⟩ : syracuseStep 2362553 = 1771915) B1771915
theorem B5999831 : Blo 698317 5999831 := bstep (se 1 (by rfl) ⟨4499873, by rfl⟩ : syracuseStep 5999831 = 8999747) B8999747
theorem B2362715 : Blo 698317 2362715 := bstep (se 1 (by rfl) ⟨1772036, by rfl⟩ : syracuseStep 2362715 = 3544073) B3544073
theorem B1576313 : Blo 698317 1576313 := bstep (se 2 (by rfl) ⟨591117, by rfl⟩ : syracuseStep 1576313 = 1182235) B1182235
theorem B2559371 : Blo 698317 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B1576619 : Blo 698317 1576619 := bstep (se 1 (by rfl) ⟨1182464, by rfl⟩ : syracuseStep 1576619 = 2364929) B2364929
theorem B1052543 : Blo 698317 1052543 := bstep (se 1 (by rfl) ⟨789407, by rfl⟩ : syracuseStep 1052543 = 1578815) B1578815
theorem B1576943 : Blo 698317 1576943 := bstep (se 1 (by rfl) ⟨1182707, by rfl⟩ : syracuseStep 1576943 = 2365415) B2365415
theorem B1183727 : Blo 698317 1183727 := bstep (se 1 (by rfl) ⟨887795, by rfl⟩ : syracuseStep 1183727 = 1775591) B1775591
theorem B1577015 : Blo 698317 1577015 := bstep (se 1 (by rfl) ⟨1182761, by rfl⟩ : syracuseStep 1577015 = 2365523) B2365523
theorem B1052735 : Blo 698317 1052735 := bstep (se 1 (by rfl) ⟨789551, by rfl⟩ : syracuseStep 1052735 = 1579103) B1579103
theorem B12161177 : Blo 698317 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B2986145 : Blo 698317 2986145 := bstep (se 2 (by rfl) ⟨1119804, by rfl⟩ : syracuseStep 2986145 = 2239609) B2239609
theorem B1577159 : Blo 698317 1577159 := bstep (se 1 (by rfl) ⟨1182869, by rfl⟩ : syracuseStep 1577159 = 2365739) B2365739
theorem B1052969 : Blo 698317 1052969 := bstep (se 2 (by rfl) ⟨394863, by rfl⟩ : syracuseStep 1052969 = 789727) B789727
theorem B1577339 : Blo 698317 1577339 := bstep (se 1 (by rfl) ⟨1183004, by rfl⟩ : syracuseStep 1577339 = 2366009) B2366009
theorem B1053239 : Blo 698317 1053239 := bstep (se 1 (by rfl) ⟨789929, by rfl⟩ : syracuseStep 1053239 = 1579859) B1579859
theorem B4788809 : Blo 698317 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B1577609 : Blo 698317 1577609 := bstep (se 2 (by rfl) ⟨591603, by rfl⟩ : syracuseStep 1577609 = 1183207) B1183207
theorem B23368333 : Blo 698317 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B11997881 : Blo 698317 11997881 := bstep (se 2 (by rfl) ⟨4499205, by rfl⟩ : syracuseStep 11997881 = 8998411) B8998411
theorem B8983649 : Blo 698317 8983649 := bstep (se 2 (by rfl) ⟨3368868, by rfl⟩ : syracuseStep 8983649 = 6737737) B6737737
theorem B2659513 : Blo 698317 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B2528441 : Blo 698317 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B2364605 : Blo 698317 2364605 := bstep (se 3 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 2364605 = 886727) B886727
theorem B2364713 : Blo 698317 2364713 := bstep (se 2 (by rfl) ⟨886767, by rfl⟩ : syracuseStep 2364713 = 1773535) B1773535
theorem B5969213 : Blo 698317 5969213 := bstep (se 3 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 5969213 = 2238455) B2238455
theorem B1578347 : Blo 698317 1578347 := bstep (se 1 (by rfl) ⟨1183760, by rfl⟩ : syracuseStep 1578347 = 2367521) B2367521
theorem B1119727 : Blo 698317 1119727 := bstep (se 1 (by rfl) ⟨839795, by rfl⟩ : syracuseStep 1119727 = 1679591) B1679591
theorem B1578617 : Blo 698317 1578617 := bstep (se 2 (by rfl) ⟨591981, by rfl⟩ : syracuseStep 1578617 = 1183963) B1183963
theorem B6723283 : Blo 698317 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B2365307 : Blo 698317 2365307 := bstep (se 1 (by rfl) ⟨1773980, by rfl⟩ : syracuseStep 2365307 = 3547961) B3547961
theorem B1578977 : Blo 698317 1578977 := bstep (se 2 (by rfl) ⟨592116, by rfl⟩ : syracuseStep 1578977 = 1184233) B1184233
theorem B11376683 : Blo 698317 11376683 := bstep (se 1 (by rfl) ⟨8532512, by rfl⟩ : syracuseStep 11376683 = 17065025) B17065025
theorem B2365577 : Blo 698317 2365577 := bstep (se 2 (by rfl) ⟨887091, by rfl⟩ : syracuseStep 2365577 = 1774183) B1774183
theorem B1775753 : Blo 698317 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B2529767 : Blo 698317 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B2399033 : Blo 698317 2399033 := bstep (se 2 (by rfl) ⟨899637, by rfl⟩ : syracuseStep 2399033 = 1799275) B1799275
theorem B1678151 : Blo 698317 1678151 := bstep (se 1 (by rfl) ⟨1258613, by rfl⟩ : syracuseStep 1678151 = 2517227) B2517227
theorem B8986625 : Blo 698317 8986625 := bstep (se 2 (by rfl) ⟨3369984, by rfl⟩ : syracuseStep 8986625 = 6739969) B6739969
theorem B1417609 : Blo 698317 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B2990519 : Blo 698317 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B1679899 : Blo 698317 1679899 := bstep (se 1 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 1679899 = 2519849) B2519849
theorem B5972561 : Blo 698317 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B6071059 : Blo 698317 6071059 := bstep (se 1 (by rfl) ⟨4553294, by rfl⟩ : syracuseStep 6071059 = 9106589) B9106589
theorem B9118493 : Blo 698317 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B27730945 : Blo 698317 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B1680659 : Blo 698317 1680659 := bstep (se 1 (by rfl) ⟨1260494, by rfl⟩ : syracuseStep 1680659 = 2520989) B2520989
theorem B698335 : Blo 698317 698335 := bstep (se 1 (by rfl) ⟨523751, by rfl⟩ : syracuseStep 698335 = 1047503) B1047503
theorem B698395 : Blo 698317 698395 := bstep (se 1 (by rfl) ⟨523796, by rfl⟩ : syracuseStep 698395 = 1047593) B1047593
theorem B698399 : Blo 698317 698399 := bstep (se 1 (by rfl) ⟨523799, by rfl⟩ : syracuseStep 698399 = 1047599) B1047599
theorem B698415 : Blo 698317 698415 := bstep (se 1 (by rfl) ⟨523811, by rfl⟩ : syracuseStep 698415 = 1047623) B1047623
theorem B698591 : Blo 698317 698591 := bstep (se 1 (by rfl) ⟨523943, by rfl⟩ : syracuseStep 698591 = 1047887) B1047887
theorem B3549419 : Blo 698317 3549419 := bstep (se 1 (by rfl) ⟨2662064, by rfl⟩ : syracuseStep 3549419 = 5324129) B5324129
theorem B698651 : Blo 698317 698651 := bstep (se 1 (by rfl) ⟨523988, by rfl⟩ : syracuseStep 698651 = 1047977) B1047977
theorem B698751 : Blo 698317 698751 := bstep (se 1 (by rfl) ⟨524063, by rfl⟩ : syracuseStep 698751 = 1048127) B1048127
theorem B698927 : Blo 698317 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B698983 : Blo 698317 698983 := bstep (se 1 (by rfl) ⟨524237, by rfl⟩ : syracuseStep 698983 = 1048475) B1048475
theorem B699359 : Blo 698317 699359 := bstep (se 1 (by rfl) ⟨524519, by rfl⟩ : syracuseStep 699359 = 1049039) B1049039
theorem B699387 : Blo 698317 699387 := bstep (se 1 (by rfl) ⟨524540, by rfl⟩ : syracuseStep 699387 = 1049081) B1049081
theorem B699455 : Blo 698317 699455 := bstep (se 1 (by rfl) ⟨524591, by rfl⟩ : syracuseStep 699455 = 1049183) B1049183
theorem B1518761 : Blo 698317 1518761 := bstep (se 2 (by rfl) ⟨569535, by rfl⟩ : syracuseStep 1518761 = 1139071) B1139071
theorem B1682743 : Blo 698317 1682743 := bstep (se 1 (by rfl) ⟨1262057, by rfl⟩ : syracuseStep 1682743 = 2524115) B2524115
theorem B699775 : Blo 698317 699775 := bstep (se 1 (by rfl) ⟨524831, by rfl⟩ : syracuseStep 699775 = 1049663) B1049663
theorem B699803 : Blo 698317 699803 := bstep (se 1 (by rfl) ⟨524852, by rfl⟩ : syracuseStep 699803 = 1049705) B1049705
theorem B699871 : Blo 698317 699871 := bstep (se 1 (by rfl) ⟨524903, by rfl⟩ : syracuseStep 699871 = 1049807) B1049807
theorem B700007 : Blo 698317 700007 := bstep (se 1 (by rfl) ⟨525005, by rfl⟩ : syracuseStep 700007 = 1050011) B1050011
theorem B45428363 : Blo 698317 45428363 := bstep (se 1 (by rfl) ⟨34071272, by rfl⟩ : syracuseStep 45428363 = 68142545) B68142545
theorem B700155 : Blo 698317 700155 := bstep (se 1 (by rfl) ⟨525116, by rfl⟩ : syracuseStep 700155 = 1050233) B1050233
theorem B700223 : Blo 698317 700223 := bstep (se 1 (by rfl) ⟨525167, by rfl⟩ : syracuseStep 700223 = 1050335) B1050335
theorem B3551039 : Blo 698317 3551039 := bstep (se 1 (by rfl) ⟨2663279, by rfl⟩ : syracuseStep 3551039 = 5326559) B5326559
theorem B2666303 : Blo 698317 2666303 := bstep (se 1 (by rfl) ⟨1999727, by rfl⟩ : syracuseStep 2666303 = 3999455) B3999455
theorem B700287 : Blo 698317 700287 := bstep (se 1 (by rfl) ⟨525215, by rfl⟩ : syracuseStep 700287 = 1050431) B1050431
theorem B700399 : Blo 698317 700399 := bstep (se 1 (by rfl) ⟨525299, by rfl⟩ : syracuseStep 700399 = 1050599) B1050599
theorem B700411 : Blo 698317 700411 := bstep (se 1 (by rfl) ⟨525308, by rfl⟩ : syracuseStep 700411 = 1050617) B1050617
theorem B2994209 : Blo 698317 2994209 := bstep (se 2 (by rfl) ⟨1122828, by rfl⟩ : syracuseStep 2994209 = 2245657) B2245657
theorem B700479 : Blo 698317 700479 := bstep (se 1 (by rfl) ⟨525359, by rfl⟩ : syracuseStep 700479 = 1050719) B1050719
theorem B700519 : Blo 698317 700519 := bstep (se 1 (by rfl) ⟨525389, by rfl⟩ : syracuseStep 700519 = 1050779) B1050779
theorem B700543 : Blo 698317 700543 := bstep (se 1 (by rfl) ⟨525407, by rfl⟩ : syracuseStep 700543 = 1050815) B1050815
theorem B700571 : Blo 698317 700571 := bstep (se 1 (by rfl) ⟨525428, by rfl⟩ : syracuseStep 700571 = 1050857) B1050857
theorem B12103937 : Blo 698317 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B700775 : Blo 698317 700775 := bstep (se 1 (by rfl) ⟨525581, by rfl⟩ : syracuseStep 700775 = 1051163) B1051163
theorem B700827 : Blo 698317 700827 := bstep (se 1 (by rfl) ⟨525620, by rfl⟩ : syracuseStep 700827 = 1051241) B1051241
theorem B11809223 : Blo 698317 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B3551687 : Blo 698317 3551687 := bstep (se 1 (by rfl) ⟨2663765, by rfl⟩ : syracuseStep 3551687 = 5327531) B5327531
theorem B28750301 : Blo 698317 28750301 := bstep (se 3 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 28750301 = 10781363) B10781363
theorem B701179 : Blo 698317 701179 := bstep (se 1 (by rfl) ⟨525884, by rfl⟩ : syracuseStep 701179 = 1051769) B1051769
theorem B701247 : Blo 698317 701247 := bstep (se 1 (by rfl) ⟨525935, by rfl⟩ : syracuseStep 701247 = 1051871) B1051871
theorem B701275 : Blo 698317 701275 := bstep (se 1 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 701275 = 1051913) B1051913
theorem B701343 : Blo 698317 701343 := bstep (se 1 (by rfl) ⟨526007, by rfl⟩ : syracuseStep 701343 = 1052015) B1052015
theorem B701423 : Blo 698317 701423 := bstep (se 1 (by rfl) ⟨526067, by rfl⟩ : syracuseStep 701423 = 1052135) B1052135
theorem B2241607 : Blo 698317 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B701511 : Blo 698317 701511 := bstep (se 1 (by rfl) ⟨526133, by rfl⟩ : syracuseStep 701511 = 1052267) B1052267
theorem B701595 : Blo 698317 701595 := bstep (se 1 (by rfl) ⟨526196, by rfl⟩ : syracuseStep 701595 = 1052393) B1052393
theorem B898231 : Blo 698317 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B701691 : Blo 698317 701691 := bstep (se 1 (by rfl) ⟨526268, by rfl⟩ : syracuseStep 701691 = 1052537) B1052537
theorem B701759 : Blo 698317 701759 := bstep (se 1 (by rfl) ⟨526319, by rfl⟩ : syracuseStep 701759 = 1052639) B1052639
theorem B2995643 : Blo 698317 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B701927 : Blo 698317 701927 := bstep (se 1 (by rfl) ⟨526445, by rfl⟩ : syracuseStep 701927 = 1052891) B1052891
theorem B701935 : Blo 698317 701935 := bstep (se 1 (by rfl) ⟨526451, by rfl⟩ : syracuseStep 701935 = 1052903) B1052903
theorem B702043 : Blo 698317 702043 := bstep (se 1 (by rfl) ⟨526532, by rfl⟩ : syracuseStep 702043 = 1053065) B1053065
theorem B702107 : Blo 698317 702107 := bstep (se 1 (by rfl) ⟨526580, by rfl⟩ : syracuseStep 702107 = 1053161) B1053161
theorem B702191 : Blo 698317 702191 := bstep (se 1 (by rfl) ⟨526643, by rfl⟩ : syracuseStep 702191 = 1053287) B1053287
theorem B702279 : Blo 698317 702279 := bstep (se 1 (by rfl) ⟨526709, by rfl⟩ : syracuseStep 702279 = 1053419) B1053419
theorem B702299 : Blo 698317 702299 := bstep (se 1 (by rfl) ⟨526724, by rfl⟩ : syracuseStep 702299 = 1053449) B1053449
theorem B5978711 : Blo 698317 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B1325801 : Blo 698317 1325801 := bstep (se 2 (by rfl) ⟨497175, by rfl⟩ : syracuseStep 1325801 = 994351) B994351
theorem B6077263 : Blo 698317 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B3783905 : Blo 698317 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B5324615 : Blo 698317 5324615 := bstep (se 1 (by rfl) ⟨3993461, by rfl⟩ : syracuseStep 5324615 = 7986923) B7986923
theorem B24199019 : Blo 698317 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B2834297 : Blo 698317 2834297 := bstep (se 2 (by rfl) ⟨1062861, by rfl⟩ : syracuseStep 2834297 = 2125723) B2125723
theorem B6734015 : Blo 698317 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B3359335 : Blo 698317 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B1328071 : Blo 698317 1328071 := bstep (se 1 (by rfl) ⟨996053, by rfl⟩ : syracuseStep 1328071 = 1992107) B1992107
theorem B3982391 : Blo 698317 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B5981309 : Blo 698317 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B4605119 : Blo 698317 4605119 := bstep (se 1 (by rfl) ⟨3453839, by rfl⟩ : syracuseStep 4605119 = 6907679) B6907679
theorem B1328815 : Blo 698317 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B1264423 : Blo 698317 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B5328017 : Blo 698317 5328017 := bstep (se 2 (by rfl) ⟨1998006, by rfl⟩ : syracuseStep 5328017 = 3996013) B3996013
theorem B6835745 : Blo 698317 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B3985307 : Blo 698317 3985307 := bstep (se 1 (by rfl) ⟨2988980, by rfl⟩ : syracuseStep 3985307 = 5977961) B5977961
theorem B20140325 : Blo 698317 20140325 := bstep (se 4 (by rfl) ⟨1888155, by rfl⟩ : syracuseStep 20140325 = 3776311) B3776311
theorem B708967 : Blo 698317 708967 := bstep (se 1 (by rfl) ⟨531725, by rfl⟩ : syracuseStep 708967 = 1063451) B1063451
theorem B1331579 : Blo 698317 1331579 := bstep (se 1 (by rfl) ⟨998684, by rfl⟩ : syracuseStep 1331579 = 1997369) B1997369
theorem B6378659 : Blo 698317 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B1332521 : Blo 698317 1332521 := bstep (se 2 (by rfl) ⟨499695, by rfl⟩ : syracuseStep 1332521 = 999391) B999391
theorem B5330447 : Blo 698317 5330447 := bstep (se 1 (by rfl) ⟨3997835, by rfl⟩ : syracuseStep 5330447 = 7995671) B7995671
theorem B3365009 : Blo 698317 3365009 := bstep (se 2 (by rfl) ⟨1261878, by rfl⟩ : syracuseStep 3365009 = 2523757) B2523757
theorem B6838715 : Blo 698317 6838715 := bstep (se 1 (by rfl) ⟨5129036, by rfl⟩ : syracuseStep 6838715 = 10258073) B10258073
theorem B1989191 : Blo 698317 1989191 := bstep (se 1 (by rfl) ⟨1491893, by rfl⟩ : syracuseStep 1989191 = 2983787) B2983787
theorem B1989431 : Blo 698317 1989431 := bstep (se 1 (by rfl) ⟨1492073, by rfl⟩ : syracuseStep 1989431 = 2984147) B2984147
theorem B1891183 : Blo 698317 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B25484257 : Blo 698317 25484257 := bstep (se 2 (by rfl) ⟨9556596, by rfl⟩ : syracuseStep 25484257 = 19113193) B19113193
theorem B13458797 : Blo 698317 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B2841965 : Blo 698317 2841965 := bstep (se 3 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 2841965 = 1065737) B1065737
theorem B1498745 : Blo 698317 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B6381359 : Blo 698317 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B8970527 : Blo 698317 8970527 := bstep (se 1 (by rfl) ⟨6727895, by rfl⟩ : syracuseStep 8970527 = 13455791) B13455791
theorem B746015 : Blo 698317 746015 := bstep (se 1 (by rfl) ⟨559511, by rfl⟩ : syracuseStep 746015 = 1119023) B1119023
theorem B3039979 : Blo 698317 3039979 := bstep (se 1 (by rfl) ⟨2279984, by rfl⟩ : syracuseStep 3039979 = 4559969) B4559969
theorem B23029069 : Blo 698317 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B3368699 : Blo 698317 3368699 := bstep (se 1 (by rfl) ⟨2526524, by rfl⟩ : syracuseStep 3368699 = 5053049) B5053049
theorem B6744161 : Blo 698317 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B14379241 : Blo 698317 14379241 := bstep (se 2 (by rfl) ⟨5392215, by rfl⟩ : syracuseStep 14379241 = 10784431) B10784431
theorem B11364745 : Blo 698317 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B5401025 : Blo 698317 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B6810113 : Blo 698317 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B34040519 : Blo 698317 34040519 := bstep (se 1 (by rfl) ⟨25530389, by rfl⟩ : syracuseStep 34040519 = 51060779) B51060779
theorem B3239357 : Blo 698317 3239357 := bstep (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) B1214759
theorem B43085267 : Blo 698317 43085267 := bstep (se 1 (by rfl) ⟨32313950, by rfl⟩ : syracuseStep 43085267 = 64627901) B64627901
theorem B5043131 : Blo 698317 5043131 := bstep (se 1 (by rfl) ⟨3782348, by rfl⟩ : syracuseStep 5043131 = 7564697) B7564697
theorem B3994555 : Blo 698317 3994555 := bstep (se 1 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 3994555 = 5991833) B5991833
theorem B717979 : Blo 698317 717979 := bstep (se 1 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 717979 = 1076969) B1076969
theorem B3536135 : Blo 698317 3536135 := bstep (se 1 (by rfl) ⟨2652101, by rfl⟩ : syracuseStep 3536135 = 5304203) B5304203
theorem B5993747 : Blo 698317 5993747 := bstep (se 1 (by rfl) ⟨4495310, by rfl⟩ : syracuseStep 5993747 = 8990621) B8990621
theorem B5305661 : Blo 698317 5305661 := bstep (se 3 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 5305661 = 1989623) B1989623
theorem B184251743 : Blo 698317 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B49903057 : Blo 698317 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B5306633 : Blo 698317 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B1767977 : Blo 698317 1767977 := bstep (se 2 (by rfl) ⟨662991, by rfl⟩ : syracuseStep 1767977 = 1325983) B1325983
theorem B2357801 : Blo 698317 2357801 := bstep (se 2 (by rfl) ⟨884175, by rfl⟩ : syracuseStep 2357801 = 1768351) B1768351
theorem B1768027 : Blo 698317 1768027 := bstep (se 1 (by rfl) ⟨1326020, by rfl⟩ : syracuseStep 1768027 = 2652041) B2652041
theorem B1571471 : Blo 698317 1571471 := bstep (se 1 (by rfl) ⟨1178603, by rfl⟩ : syracuseStep 1571471 = 2357207) B2357207
theorem B1571561 : Blo 698317 1571561 := bstep (se 2 (by rfl) ⟨589335, by rfl⟩ : syracuseStep 1571561 = 1178671) B1178671
theorem B2456477 : Blo 698317 2456477 := bstep (se 3 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 2456477 = 921179) B921179
theorem B1571795 : Blo 698317 1571795 := bstep (se 1 (by rfl) ⟨1178846, by rfl⟩ : syracuseStep 1571795 = 2357693) B2357693
theorem B4488317 : Blo 698317 4488317 := bstep (se 3 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 4488317 = 1683119) B1683119
theorem B1572065 : Blo 698317 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B1572371 : Blo 698317 1572371 := bstep (se 1 (by rfl) ⟨1179278, by rfl⟩ : syracuseStep 1572371 = 2358557) B2358557
theorem B1768979 : Blo 698317 1768979 := bstep (se 1 (by rfl) ⟨1326734, by rfl⟩ : syracuseStep 1768979 = 2653469) B2653469
theorem B1048175 : Blo 698317 1048175 := bstep (se 1 (by rfl) ⟨786131, by rfl⟩ : syracuseStep 1048175 = 1572263) B1572263
theorem B20512379 : Blo 698317 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B5996207 : Blo 698317 5996207 := bstep (se 1 (by rfl) ⟨4497155, by rfl⟩ : syracuseStep 5996207 = 8994311) B8994311
theorem B5308091 : Blo 698317 5308091 := bstep (se 1 (by rfl) ⟨3981068, by rfl⟩ : syracuseStep 5308091 = 7962137) B7962137
theorem B1048295 : Blo 698317 1048295 := bstep (se 1 (by rfl) ⟨786221, by rfl⟩ : syracuseStep 1048295 = 1572443) B1572443
theorem B786343 : Blo 698317 786343 := bstep (se 1 (by rfl) ⟨589757, by rfl⟩ : syracuseStep 786343 = 1179515) B1179515
theorem B1048487 : Blo 698317 1048487 := bstep (se 1 (by rfl) ⟨786365, by rfl⟩ : syracuseStep 1048487 = 1572731) B1572731
theorem B1048703 : Blo 698317 1048703 := bstep (se 1 (by rfl) ⟨786527, by rfl⟩ : syracuseStep 1048703 = 1573055) B1573055
theorem B786559 : Blo 698317 786559 := bstep (se 1 (by rfl) ⟨589919, by rfl⟩ : syracuseStep 786559 = 1179839) B1179839
theorem B4489343 : Blo 698317 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B1048991 : Blo 698317 1048991 := bstep (se 1 (by rfl) ⟨786743, by rfl⟩ : syracuseStep 1048991 = 1573487) B1573487
theorem B786847 : Blo 698317 786847 := bstep (se 1 (by rfl) ⟨590135, by rfl⟩ : syracuseStep 786847 = 1180271) B1180271
theorem B1573433 : Blo 698317 1573433 := bstep (se 2 (by rfl) ⟨590037, by rfl⟩ : syracuseStep 1573433 = 1180075) B1180075
theorem B1049255 : Blo 698317 1049255 := bstep (se 1 (by rfl) ⟨786941, by rfl⟩ : syracuseStep 1049255 = 1573883) B1573883
theorem B2654927 : Blo 698317 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B1049375 : Blo 698317 1049375 := bstep (se 1 (by rfl) ⟨787031, by rfl⟩ : syracuseStep 1049375 = 1574063) B1574063
theorem B1770295 : Blo 698317 1770295 := bstep (se 1 (by rfl) ⟨1327721, by rfl⟩ : syracuseStep 1770295 = 2655443) B2655443
theorem B1049399 : Blo 698317 1049399 := bstep (se 1 (by rfl) ⟨787049, by rfl⟩ : syracuseStep 1049399 = 1574099) B1574099
theorem B1049579 : Blo 698317 1049579 := bstep (se 1 (by rfl) ⟨787184, by rfl⟩ : syracuseStep 1049579 = 1574369) B1574369
theorem B8094745 : Blo 698317 8094745 := bstep (se 2 (by rfl) ⟨3035529, by rfl⟩ : syracuseStep 8094745 = 6071059) B6071059
theorem B2360447 : Blo 698317 2360447 := bstep (se 1 (by rfl) ⟨1770335, by rfl⟩ : syracuseStep 2360447 = 3540671) B3540671
theorem B1770731 : Blo 698317 1770731 := bstep (se 1 (by rfl) ⟨1328048, by rfl⟩ : syracuseStep 1770731 = 2656097) B2656097
theorem B1770761 : Blo 698317 1770761 := bstep (se 2 (by rfl) ⟨664035, by rfl⟩ : syracuseStep 1770761 = 1328071) B1328071
theorem B1574153 : Blo 698317 1574153 := bstep (se 2 (by rfl) ⟨590307, by rfl⟩ : syracuseStep 1574153 = 1180615) B1180615
theorem B1050089 : Blo 698317 1050089 := bstep (se 2 (by rfl) ⟨393783, by rfl⟩ : syracuseStep 1050089 = 787567) B787567
theorem B7997129 : Blo 698317 7997129 := bstep (se 2 (by rfl) ⟨2998923, by rfl⟩ : syracuseStep 7997129 = 5997847) B5997847
theorem B30705425 : Blo 698317 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B1574675 : Blo 698317 1574675 := bstep (se 1 (by rfl) ⟨1181006, by rfl⟩ : syracuseStep 1574675 = 2362013) B2362013
theorem B1050479 : Blo 698317 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B1050665 : Blo 698317 1050665 := bstep (se 2 (by rfl) ⟨393999, by rfl⟩ : syracuseStep 1050665 = 787999) B787999
theorem B1771591 : Blo 698317 1771591 := bstep (se 1 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 1771591 = 2657387) B2657387
theorem B1050695 : Blo 698317 1050695 := bstep (se 1 (by rfl) ⟨788021, by rfl⟩ : syracuseStep 1050695 = 1576043) B1576043
theorem B1575035 : Blo 698317 1575035 := bstep (se 1 (by rfl) ⟨1181276, by rfl⟩ : syracuseStep 1575035 = 2362553) B2362553
theorem B3999887 : Blo 698317 3999887 := bstep (se 1 (by rfl) ⟨2999915, by rfl⟩ : syracuseStep 3999887 = 5999831) B5999831
theorem B1575143 : Blo 698317 1575143 := bstep (se 1 (by rfl) ⟨1181357, by rfl⟩ : syracuseStep 1575143 = 2362715) B2362715
theorem B1771753 : Blo 698317 1771753 := bstep (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) B1328815
theorem B1050875 : Blo 698317 1050875 := bstep (se 1 (by rfl) ⟨788156, by rfl⟩ : syracuseStep 1050875 = 1576313) B1576313
theorem B4557163 : Blo 698317 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B1575305 : Blo 698317 1575305 := bstep (se 2 (by rfl) ⟨590739, by rfl⟩ : syracuseStep 1575305 = 1181479) B1181479
theorem B1051079 : Blo 698317 1051079 := bstep (se 1 (by rfl) ⟨788309, by rfl⟩ : syracuseStep 1051079 = 1576619) B1576619
theorem B2656871 : Blo 698317 2656871 := bstep (se 1 (by rfl) ⟨1992653, by rfl⟩ : syracuseStep 2656871 = 3985307) B3985307
theorem B1051295 : Blo 698317 1051295 := bstep (se 1 (by rfl) ⟨788471, by rfl⟩ : syracuseStep 1051295 = 1576943) B1576943
theorem B789151 : Blo 698317 789151 := bstep (se 1 (by rfl) ⟨591863, by rfl⟩ : syracuseStep 789151 = 1183727) B1183727
theorem B1051343 : Blo 698317 1051343 := bstep (se 1 (by rfl) ⟨788507, by rfl⟩ : syracuseStep 1051343 = 1577015) B1577015
theorem B1051439 : Blo 698317 1051439 := bstep (se 1 (by rfl) ⟨788579, by rfl⟩ : syracuseStep 1051439 = 1577159) B1577159
theorem B1051559 : Blo 698317 1051559 := bstep (se 1 (by rfl) ⟨788669, by rfl⟩ : syracuseStep 1051559 = 1577339) B1577339
theorem B19172321 : Blo 698317 19172321 := bstep (se 2 (by rfl) ⟨7189620, by rfl⟩ : syracuseStep 19172321 = 14379241) B14379241
theorem B1051739 : Blo 698317 1051739 := bstep (se 1 (by rfl) ⟨788804, by rfl⟩ : syracuseStep 1051739 = 1577609) B1577609
theorem B7998587 : Blo 698317 7998587 := bstep (se 1 (by rfl) ⟨5998940, by rfl⟩ : syracuseStep 7998587 = 11997881) B11997881
theorem B1051817 : Blo 698317 1051817 := bstep (se 2 (by rfl) ⟨394431, by rfl⟩ : syracuseStep 1051817 = 788863) B788863
theorem B1576403 : Blo 698317 1576403 := bstep (se 1 (by rfl) ⟨1182302, by rfl⟩ : syracuseStep 1576403 = 2364605) B2364605
theorem B1576475 : Blo 698317 1576475 := bstep (se 1 (by rfl) ⟨1182356, by rfl⟩ : syracuseStep 1576475 = 2364713) B2364713
theorem B888347 : Blo 698317 888347 := bstep (se 1 (by rfl) ⟨666260, by rfl⟩ : syracuseStep 888347 = 1332521) B1332521
theorem B1052231 : Blo 698317 1052231 := bstep (se 1 (by rfl) ⟨789173, by rfl⟩ : syracuseStep 1052231 = 1578347) B1578347
theorem B1576673 : Blo 698317 1576673 := bstep (se 2 (by rfl) ⟨591252, by rfl⟩ : syracuseStep 1576673 = 1182505) B1182505
theorem B1052411 : Blo 698317 1052411 := bstep (se 1 (by rfl) ⟨789308, by rfl⟩ : syracuseStep 1052411 = 1578617) B1578617
theorem B1576871 : Blo 698317 1576871 := bstep (se 1 (by rfl) ⟨1182653, by rfl⟩ : syracuseStep 1576871 = 2365307) B2365307
theorem B1052651 : Blo 698317 1052651 := bstep (se 1 (by rfl) ⟨789488, by rfl⟩ : syracuseStep 1052651 = 1578977) B1578977
theorem B1577033 : Blo 698317 1577033 := bstep (se 2 (by rfl) ⟨591387, by rfl⟩ : syracuseStep 1577033 = 1182775) B1182775
theorem B1577051 : Blo 698317 1577051 := bstep (se 1 (by rfl) ⟨1182788, by rfl⟩ : syracuseStep 1577051 = 2365577) B2365577
theorem B1183835 : Blo 698317 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B1118767 : Blo 698317 1118767 := bstep (se 1 (by rfl) ⟨839075, by rfl⟩ : syracuseStep 1118767 = 1678151) B1678151
theorem B1120439 : Blo 698317 1120439 := bstep (se 1 (by rfl) ⟨840329, by rfl⟩ : syracuseStep 1120439 = 1680659) B1680659
theorem B18160301 : Blo 698317 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B4496107 : Blo 698317 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B2988809 : Blo 698317 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B2366279 : Blo 698317 2366279 := bstep (se 1 (by rfl) ⟨1774709, by rfl⟩ : syracuseStep 2366279 = 3549419) B3549419
theorem B957305 : Blo 698317 957305 := bstep (se 2 (by rfl) ⟨358989, by rfl⟩ : syracuseStep 957305 = 717979) B717979
theorem B3546017 : Blo 698317 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B30285575 : Blo 698317 30285575 := bstep (se 1 (by rfl) ⟨22714181, by rfl⟩ : syracuseStep 30285575 = 45428363) B45428363
theorem B2367359 : Blo 698317 2367359 := bstep (se 1 (by rfl) ⟨1775519, by rfl⟩ : syracuseStep 2367359 = 3551039) B3551039
theorem B1777535 : Blo 698317 1777535 := bstep (se 1 (by rfl) ⟨1333151, by rfl⟩ : syracuseStep 1777535 = 2666303) B2666303
theorem B5971877 : Blo 698317 5971877 := bstep (se 4 (by rfl) ⟨559863, by rfl⟩ : syracuseStep 5971877 = 1119727) B1119727
theorem B8069291 : Blo 698317 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B7872815 : Blo 698317 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B2367791 : Blo 698317 2367791 := bstep (se 1 (by rfl) ⟨1775843, by rfl⟩ : syracuseStep 2367791 = 3551687) B3551687
theorem B6824989 : Blo 698317 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B8103017 : Blo 698317 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B2992211 : Blo 698317 2992211 := bstep (se 1 (by rfl) ⟨2244158, by rfl⟩ : syracuseStep 2992211 = 4488317) B4488317
theorem B698783 : Blo 698317 698783 := bstep (se 1 (by rfl) ⟨524087, by rfl⟩ : syracuseStep 698783 = 1048175) B1048175
theorem B13674919 : Blo 698317 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B698863 : Blo 698317 698863 := bstep (se 1 (by rfl) ⟨524147, by rfl⟩ : syracuseStep 698863 = 1048295) B1048295
theorem B3549743 : Blo 698317 3549743 := bstep (se 1 (by rfl) ⟨2662307, by rfl⟩ : syracuseStep 3549743 = 5324615) B5324615
theorem B16132679 : Blo 698317 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B698991 : Blo 698317 698991 := bstep (se 1 (by rfl) ⟨524243, by rfl⟩ : syracuseStep 698991 = 1048487) B1048487
theorem B699207 : Blo 698317 699207 := bstep (se 1 (by rfl) ⟨524405, by rfl⟩ : syracuseStep 699207 = 1048811) B1048811
theorem B699247 : Blo 698317 699247 := bstep (se 1 (by rfl) ⟨524435, by rfl⟩ : syracuseStep 699247 = 1048871) B1048871
theorem B699695 : Blo 698317 699695 := bstep (se 1 (by rfl) ⟨524771, by rfl⟩ : syracuseStep 699695 = 1049543) B1049543
theorem B2239865 : Blo 698317 2239865 := bstep (se 2 (by rfl) ⟨839949, by rfl⟩ : syracuseStep 2239865 = 1679899) B1679899
theorem B699807 : Blo 698317 699807 := bstep (se 1 (by rfl) ⟨524855, by rfl⟩ : syracuseStep 699807 = 1049711) B1049711
theorem B699935 : Blo 698317 699935 := bstep (se 1 (by rfl) ⟨524951, by rfl⟩ : syracuseStep 699935 = 1049903) B1049903
theorem B3550877 : Blo 698317 3550877 := bstep (se 3 (by rfl) ⟨665789, by rfl⟩ : syracuseStep 3550877 = 1331579) B1331579
theorem B700071 : Blo 698317 700071 := bstep (se 1 (by rfl) ⟨525053, by rfl⟩ : syracuseStep 700071 = 1050107) B1050107
theorem B700095 : Blo 698317 700095 := bstep (se 1 (by rfl) ⟨525071, by rfl⟩ : syracuseStep 700095 = 1050143) B1050143
theorem B700191 : Blo 698317 700191 := bstep (se 1 (by rfl) ⟨525143, by rfl⟩ : syracuseStep 700191 = 1050287) B1050287
theorem B700271 : Blo 698317 700271 := bstep (se 1 (by rfl) ⟨525203, by rfl⟩ : syracuseStep 700271 = 1050407) B1050407
theorem B36974593 : Blo 698317 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B700639 : Blo 698317 700639 := bstep (se 1 (by rfl) ⟨525479, by rfl⟩ : syracuseStep 700639 = 1050959) B1050959
theorem B700671 : Blo 698317 700671 := bstep (se 1 (by rfl) ⟨525503, by rfl⟩ : syracuseStep 700671 = 1051007) B1051007
theorem B700699 : Blo 698317 700699 := bstep (se 1 (by rfl) ⟨525524, by rfl⟩ : syracuseStep 700699 = 1051049) B1051049
theorem B700955 : Blo 698317 700955 := bstep (se 1 (by rfl) ⟨525716, by rfl⟩ : syracuseStep 700955 = 1051433) B1051433
theorem B701095 : Blo 698317 701095 := bstep (se 1 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 701095 = 1051643) B1051643
theorem B701135 : Blo 698317 701135 := bstep (se 1 (by rfl) ⟨525851, by rfl⟩ : syracuseStep 701135 = 1051703) B1051703
theorem B3552011 : Blo 698317 3552011 := bstep (se 1 (by rfl) ⟨2664008, by rfl⟩ : syracuseStep 3552011 = 5328017) B5328017
theorem B701215 : Blo 698317 701215 := bstep (se 1 (by rfl) ⟨525911, by rfl⟩ : syracuseStep 701215 = 1051823) B1051823
theorem B701695 : Blo 698317 701695 := bstep (se 1 (by rfl) ⟨526271, by rfl⟩ : syracuseStep 701695 = 1052543) B1052543
theorem B701823 : Blo 698317 701823 := bstep (se 1 (by rfl) ⟨526367, by rfl⟩ : syracuseStep 701823 = 1052735) B1052735
theorem B8107451 : Blo 698317 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B701979 : Blo 698317 701979 := bstep (se 1 (by rfl) ⟨526484, by rfl⟩ : syracuseStep 701979 = 1052969) B1052969
theorem B702159 : Blo 698317 702159 := bstep (se 1 (by rfl) ⟨526619, by rfl⟩ : syracuseStep 702159 = 1053239) B1053239
theorem B3192539 : Blo 698317 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B15152993 : Blo 698317 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B1685627 : Blo 698317 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B3979475 : Blo 698317 3979475 := bstep (se 1 (by rfl) ⟨2984606, by rfl⟩ : syracuseStep 3979475 = 5969213) B5969213
theorem B3553631 : Blo 698317 3553631 := bstep (se 1 (by rfl) ⟨2665223, by rfl⟩ : syracuseStep 3553631 = 5330447) B5330447
theorem B1685897 : Blo 698317 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B7584455 : Blo 698317 7584455 := bstep (se 1 (by rfl) ⟨5688341, by rfl⟩ : syracuseStep 7584455 = 11376683) B11376683
theorem B2243339 : Blo 698317 2243339 := bstep (se 1 (by rfl) ⟨1682504, by rfl⟩ : syracuseStep 2243339 = 3365009) B3365009
theorem B1686511 : Blo 698317 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B1326127 : Blo 698317 1326127 := bstep (se 1 (by rfl) ⟨994595, by rfl⟩ : syracuseStep 1326127 = 1989191) B1989191
theorem B2243657 : Blo 698317 2243657 := bstep (se 2 (by rfl) ⟨841371, by rfl⟩ : syracuseStep 2243657 = 1682743) B1682743
theorem B1326287 : Blo 698317 1326287 := bstep (se 1 (by rfl) ⟨994715, by rfl⟩ : syracuseStep 1326287 = 1989431) B1989431
theorem B999163 : Blo 698317 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B5980351 : Blo 698317 5980351 := bstep (se 1 (by rfl) ⟨4485263, by rfl⟩ : syracuseStep 5980351 = 8970527) B8970527
theorem B3981707 : Blo 698317 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B6078995 : Blo 698317 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B18236573 : Blo 698317 18236573 := bstep (se 3 (by rfl) ⟨3419357, by rfl⟩ : syracuseStep 18236573 = 6838715) B6838715
theorem B2245799 : Blo 698317 2245799 := bstep (se 1 (by rfl) ⟨1684349, by rfl⟩ : syracuseStep 2245799 = 3368699) B3368699
theorem B5326073 : Blo 698317 5326073 := bstep (se 2 (by rfl) ⟨1997277, by rfl⟩ : syracuseStep 5326073 = 3994555) B3994555
theorem B1197641 : Blo 698317 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B22693679 : Blo 698317 22693679 := bstep (se 1 (by rfl) ⟨17020259, by rfl⟩ : syracuseStep 22693679 = 34040519) B34040519
theorem B66537409 : Blo 698317 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B8964377 : Blo 698317 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B28723511 : Blo 698317 28723511 := bstep (se 1 (by rfl) ⟨21542633, by rfl⟩ : syracuseStep 28723511 = 43085267) B43085267
theorem B3362087 : Blo 698317 3362087 := bstep (se 1 (by rfl) ⟨2521565, by rfl⟩ : syracuseStep 3362087 = 5043131) B5043131
theorem B122834495 : Blo 698317 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B8638285 : Blo 698317 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B3985807 : Blo 698317 3985807 := bstep (se 1 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 3985807 = 5978711) B5978711
theorem B1889531 : Blo 698317 1889531 := bstep (se 1 (by rfl) ⟨1417148, by rfl⟩ : syracuseStep 1889531 = 2834297) B2834297
theorem B1890145 : Blo 698317 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B3987539 : Blo 698317 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B3070079 : Blo 698317 3070079 := bstep (se 1 (by rfl) ⟨2302559, by rfl⟩ : syracuseStep 3070079 = 4605119) B4605119
theorem B4479113 : Blo 698317 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B4053305 : Blo 698317 4053305 := bstep (se 2 (by rfl) ⟨1519989, by rfl⟩ : syracuseStep 4053305 = 3039979) B3039979
theorem B4479371 : Blo 698317 4479371 := bstep (se 1 (by rfl) ⟨3359528, by rfl⟩ : syracuseStep 4479371 = 6719057) B6719057
theorem B1989373 : Blo 698317 1989373 := bstep (se 3 (by rfl) ⟨373007, by rfl⟩ : syracuseStep 1989373 = 746015) B746015
theorem B5331905 : Blo 698317 5331905 := bstep (se 2 (by rfl) ⟨1999464, by rfl⟩ : syracuseStep 5331905 = 3998929) B3998929
theorem B1990763 : Blo 698317 1990763 := bstep (se 1 (by rfl) ⟨1493072, by rfl⟩ : syracuseStep 1990763 = 2986145) B2986145
theorem B13426883 : Blo 698317 13426883 := bstep (se 1 (by rfl) ⟨10070162, by rfl⟩ : syracuseStep 13426883 = 20140325) B20140325
theorem B5989099 : Blo 698317 5989099 := bstep (se 1 (by rfl) ⟨4491824, by rfl⟩ : syracuseStep 5989099 = 8983649) B8983649
theorem B4252439 : Blo 698317 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B7988381 : Blo 698317 7988381 := bstep (se 3 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 7988381 = 2995643) B2995643
theorem B1599355 : Blo 698317 1599355 := bstep (se 1 (by rfl) ⟨1199516, by rfl⟩ : syracuseStep 1599355 = 2399033) B2399033
theorem B8972531 : Blo 698317 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B1894643 : Blo 698317 1894643 := bstep (se 1 (by rfl) ⟨1420982, by rfl⟩ : syracuseStep 1894643 = 2841965) B2841965
theorem B4254239 : Blo 698317 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B5991083 : Blo 698317 5991083 := bstep (se 1 (by rfl) ⟨4493312, by rfl⟩ : syracuseStep 5991083 = 8986625) B8986625
theorem B1993679 : Blo 698317 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B945289 : Blo 698317 945289 := bstep (se 2 (by rfl) ⟨354483, by rfl⟩ : syracuseStep 945289 = 708967) B708967
theorem B31157777 : Blo 698317 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B3600683 : Blo 698317 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B1012507 : Blo 698317 1012507 := bstep (se 1 (by rfl) ⟨759380, by rfl⟩ : syracuseStep 1012507 = 1518761) B1518761
theorem B1996139 : Blo 698317 1996139 := bstep (se 1 (by rfl) ⟨1497104, by rfl⟩ : syracuseStep 1996139 = 2994209) B2994209
theorem B19166867 : Blo 698317 19166867 := bstep (se 1 (by rfl) ⟨14375150, by rfl⟩ : syracuseStep 19166867 = 28750301) B28750301
theorem B2357369 : Blo 698317 2357369 := bstep (se 2 (by rfl) ⟨884013, by rfl⟩ : syracuseStep 2357369 = 1768027) B1768027
theorem B2357423 : Blo 698317 2357423 := bstep (se 1 (by rfl) ⟨1768067, by rfl⟩ : syracuseStep 2357423 = 3536135) B3536135
theorem B3995831 : Blo 698317 3995831 := bstep (se 1 (by rfl) ⟨2996873, by rfl⟩ : syracuseStep 3995831 = 5993747) B5993747
theorem B3537107 : Blo 698317 3537107 := bstep (se 1 (by rfl) ⟨2652830, by rfl⟩ : syracuseStep 3537107 = 5305661) B5305661
theorem B2521577 : Blo 698317 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B33979009 : Blo 698317 33979009 := bstep (se 2 (by rfl) ⟨12742128, by rfl⟩ : syracuseStep 33979009 = 25484257) B25484257
theorem B3537755 : Blo 698317 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B1178651 : Blo 698317 1178651 := bstep (se 1 (by rfl) ⟨883988, by rfl⟩ : syracuseStep 1178651 = 1767977) B1767977
theorem B1571867 : Blo 698317 1571867 := bstep (se 1 (by rfl) ⟨1178900, by rfl⟩ : syracuseStep 1571867 = 2357801) B2357801
theorem B1047647 : Blo 698317 1047647 := bstep (se 1 (by rfl) ⟨785735, by rfl⟩ : syracuseStep 1047647 = 1571471) B1571471
theorem B883867 : Blo 698317 883867 := bstep (se 1 (by rfl) ⟨662900, by rfl⟩ : syracuseStep 883867 = 1325801) B1325801
theorem B1047707 : Blo 698317 1047707 := bstep (se 1 (by rfl) ⟨785780, by rfl⟩ : syracuseStep 1047707 = 1571561) B1571561
theorem B1637651 : Blo 698317 1637651 := bstep (se 1 (by rfl) ⟨1228238, by rfl⟩ : syracuseStep 1637651 = 2456477) B2456477
theorem B1047863 : Blo 698317 1047863 := bstep (se 1 (by rfl) ⟨785897, by rfl⟩ : syracuseStep 1047863 = 1571795) B1571795
theorem B1048043 : Blo 698317 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B2522603 : Blo 698317 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B1048247 : Blo 698317 1048247 := bstep (se 1 (by rfl) ⟨786185, by rfl⟩ : syracuseStep 1048247 = 1572371) B1572371
theorem B1179319 : Blo 698317 1179319 := bstep (se 1 (by rfl) ⟨884489, by rfl⟩ : syracuseStep 1179319 = 1768979) B1768979
theorem B3997471 : Blo 698317 3997471 := bstep (se 1 (by rfl) ⟨2998103, by rfl⟩ : syracuseStep 3997471 = 5996207) B5996207
theorem B3538727 : Blo 698317 3538727 := bstep (se 1 (by rfl) ⟨2654045, by rfl⟩ : syracuseStep 3538727 = 5308091) B5308091
theorem B1048457 : Blo 698317 1048457 := bstep (se 2 (by rfl) ⟨393171, by rfl⟩ : syracuseStep 1048457 = 786343) B786343
theorem B1048745 : Blo 698317 1048745 := bstep (se 2 (by rfl) ⟨393279, by rfl⟩ : syracuseStep 1048745 = 786559) B786559
theorem B2654471 : Blo 698317 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B1048955 : Blo 698317 1048955 := bstep (se 1 (by rfl) ⟨786716, by rfl⟩ : syracuseStep 1048955 = 1573433) B1573433
theorem B1769951 : Blo 698317 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B1049129 : Blo 698317 1049129 := bstep (se 2 (by rfl) ⟨393423, by rfl⟩ : syracuseStep 1049129 = 786847) B786847
theorem B1573631 : Blo 698317 1573631 := bstep (se 1 (by rfl) ⟨1180223, by rfl⟩ : syracuseStep 1573631 = 2360447) B2360447
theorem B12157715 : Blo 698317 12157715 := bstep (se 1 (by rfl) ⟨9118286, by rfl⟩ : syracuseStep 12157715 = 18236573) B18236573
theorem B1180487 : Blo 698317 1180487 := bstep (se 1 (by rfl) ⟨885365, by rfl⟩ : syracuseStep 1180487 = 1770731) B1770731
theorem B1180507 : Blo 698317 1180507 := bstep (se 1 (by rfl) ⟨885380, by rfl⟩ : syracuseStep 1180507 = 1770761) B1770761
theorem B1049435 : Blo 698317 1049435 := bstep (se 1 (by rfl) ⟨787076, by rfl⟩ : syracuseStep 1049435 = 1574153) B1574153
theorem B2360393 : Blo 698317 2360393 := bstep (se 2 (by rfl) ⟨885147, by rfl⟩ : syracuseStep 2360393 = 1770295) B1770295
theorem B1049783 : Blo 698317 1049783 := bstep (se 1 (by rfl) ⟨787337, by rfl⟩ : syracuseStep 1049783 = 1574675) B1574675
theorem B1050023 : Blo 698317 1050023 := bstep (se 1 (by rfl) ⟨787517, by rfl⟩ : syracuseStep 1050023 = 1575035) B1575035
theorem B1050095 : Blo 698317 1050095 := bstep (se 1 (by rfl) ⟨787571, by rfl⟩ : syracuseStep 1050095 = 1575143) B1575143
theorem B1050203 : Blo 698317 1050203 := bstep (se 1 (by rfl) ⟨787652, by rfl⟩ : syracuseStep 1050203 = 1575305) B1575305
theorem B1771247 : Blo 698317 1771247 := bstep (se 1 (by rfl) ⟨1328435, by rfl⟩ : syracuseStep 1771247 = 2656871) B2656871
theorem B12781547 : Blo 698317 12781547 := bstep (se 1 (by rfl) ⟨9586160, by rfl⟩ : syracuseStep 12781547 = 19172321) B19172321
theorem B11339837 : Blo 698317 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B1050935 : Blo 698317 1050935 := bstep (se 1 (by rfl) ⟨788201, by rfl⟩ : syracuseStep 1050935 = 1576403) B1576403
theorem B1050983 : Blo 698317 1050983 := bstep (se 1 (by rfl) ⟨788237, by rfl⟩ : syracuseStep 1050983 = 1576475) B1576475
theorem B81889663 : Blo 698317 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B1051115 : Blo 698317 1051115 := bstep (se 1 (by rfl) ⟨788336, by rfl⟩ : syracuseStep 1051115 = 1576673) B1576673
theorem B1051247 : Blo 698317 1051247 := bstep (se 1 (by rfl) ⟨788435, by rfl⟩ : syracuseStep 1051247 = 1576871) B1576871
theorem B1051355 : Blo 698317 1051355 := bstep (se 1 (by rfl) ⟨788516, by rfl⟩ : syracuseStep 1051355 = 1577033) B1577033
theorem B1051367 : Blo 698317 1051367 := bstep (se 1 (by rfl) ⟨788525, by rfl⟩ : syracuseStep 1051367 = 1577051) B1577051
theorem B789223 : Blo 698317 789223 := bstep (se 1 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 789223 = 1183835) B1183835
theorem B2362121 : Blo 698317 2362121 := bstep (se 2 (by rfl) ⟨885795, by rfl⟩ : syracuseStep 2362121 = 1771591) B1771591
theorem B2362337 : Blo 698317 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B1052201 : Blo 698317 1052201 := bstep (se 2 (by rfl) ⟨394575, by rfl⟩ : syracuseStep 1052201 = 789151) B789151
theorem B2658359 : Blo 698317 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B2986075 : Blo 698317 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B2986247 : Blo 698317 2986247 := bstep (se 1 (by rfl) ⟨2239685, by rfl⟩ : syracuseStep 2986247 = 4479371) B4479371
theorem B1577519 : Blo 698317 1577519 := bstep (se 1 (by rfl) ⟨1183139, by rfl⟩ : syracuseStep 1577519 = 2366279) B2366279
theorem B2364011 : Blo 698317 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B20190383 : Blo 698317 20190383 := bstep (se 1 (by rfl) ⟨15142787, by rfl⟩ : syracuseStep 20190383 = 30285575) B30285575
theorem B1578239 : Blo 698317 1578239 := bstep (se 1 (by rfl) ⟨1183679, by rfl⟩ : syracuseStep 1578239 = 2367359) B2367359
theorem B1185023 : Blo 698317 1185023 := bstep (se 1 (by rfl) ⟨888767, by rfl⟩ : syracuseStep 1185023 = 1777535) B1777535
theorem B5379527 : Blo 698317 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B8951255 : Blo 698317 8951255 := bstep (se 1 (by rfl) ⟨6713441, by rfl⟩ : syracuseStep 8951255 = 13426883) B13426883
theorem B5248543 : Blo 698317 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B1578527 : Blo 698317 1578527 := bstep (se 1 (by rfl) ⟨1183895, by rfl⟩ : syracuseStep 1578527 = 2367791) B2367791
theorem B2987837 : Blo 698317 2987837 := bstep (se 3 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 2987837 = 1120439) B1120439
theorem B5314409 : Blo 698317 5314409 := bstep (se 2 (by rfl) ⟨1992903, by rfl⟩ : syracuseStep 5314409 = 3985807) B3985807
theorem B6724205 : Blo 698317 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B11344637 : Blo 698317 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2366495 : Blo 698317 2366495 := bstep (se 1 (by rfl) ⟨1774871, by rfl⟩ : syracuseStep 2366495 = 3549743) B3549743
theorem B10755119 : Blo 698317 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B2367251 : Blo 698317 2367251 := bstep (se 1 (by rfl) ⟨1775438, by rfl⟩ : syracuseStep 2367251 = 3550877) B3550877
theorem B2400455 : Blo 698317 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B2368007 : Blo 698317 2368007 := bstep (se 1 (by rfl) ⟨1776005, by rfl⟩ : syracuseStep 2368007 = 3552011) B3552011
theorem B10101995 : Blo 698317 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B2368925 : Blo 698317 2368925 := bstep (se 3 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 2368925 = 888347) B888347
theorem B1123751 : Blo 698317 1123751 := bstep (se 1 (by rfl) ⟨842813, by rfl⟩ : syracuseStep 1123751 = 1685627) B1685627
theorem B2663887 : Blo 698317 2663887 := bstep (se 1 (by rfl) ⟨1997915, by rfl⟩ : syracuseStep 2663887 = 3995831) B3995831
theorem B2369087 : Blo 698317 2369087 := bstep (se 1 (by rfl) ⟨1776815, by rfl⟩ : syracuseStep 2369087 = 3553631) B3553631
theorem B1123931 : Blo 698317 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B5056303 : Blo 698317 5056303 := bstep (se 1 (by rfl) ⟨3792227, by rfl⟩ : syracuseStep 5056303 = 7584455) B7584455
theorem B8529893 : Blo 698317 8529893 := bstep (se 4 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 8529893 = 1599355) B1599355
theorem B698431 : Blo 698317 698431 := bstep (se 1 (by rfl) ⟨523823, by rfl⟩ : syracuseStep 698431 = 1047647) B1047647
theorem B698471 : Blo 698317 698471 := bstep (se 1 (by rfl) ⟨523853, by rfl⟩ : syracuseStep 698471 = 1047707) B1047707
theorem B1091767 : Blo 698317 1091767 := bstep (se 1 (by rfl) ⟨818825, by rfl⟩ : syracuseStep 1091767 = 1637651) B1637651
theorem B698575 : Blo 698317 698575 := bstep (se 1 (by rfl) ⟨523931, by rfl⟩ : syracuseStep 698575 = 1047863) B1047863
theorem B698695 : Blo 698317 698695 := bstep (se 1 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 698695 = 1048043) B1048043
theorem B1681735 : Blo 698317 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B698831 : Blo 698317 698831 := bstep (se 1 (by rfl) ⟨524123, by rfl⟩ : syracuseStep 698831 = 1048247) B1048247
theorem B698971 : Blo 698317 698971 := bstep (se 1 (by rfl) ⟨524228, by rfl⟩ : syracuseStep 698971 = 1048457) B1048457
theorem B699135 : Blo 698317 699135 := bstep (se 1 (by rfl) ⟨524351, by rfl⟩ : syracuseStep 699135 = 1048703) B1048703
theorem B2992895 : Blo 698317 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B7973801 : Blo 698317 7973801 := bstep (se 2 (by rfl) ⟨2990175, by rfl⟩ : syracuseStep 7973801 = 5980351) B5980351
theorem B699327 : Blo 698317 699327 := bstep (se 1 (by rfl) ⟨524495, by rfl⟩ : syracuseStep 699327 = 1048991) B1048991
theorem B699503 : Blo 698317 699503 := bstep (se 1 (by rfl) ⟨524627, by rfl⟩ : syracuseStep 699503 = 1049255) B1049255
theorem B699583 : Blo 698317 699583 := bstep (se 1 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 699583 = 1049375) B1049375
theorem B699599 : Blo 698317 699599 := bstep (se 1 (by rfl) ⟨524699, by rfl⟩ : syracuseStep 699599 = 1049399) B1049399
theorem B699719 : Blo 698317 699719 := bstep (se 1 (by rfl) ⟨524789, by rfl⟩ : syracuseStep 699719 = 1049579) B1049579
theorem B3550715 : Blo 698317 3550715 := bstep (se 1 (by rfl) ⟨2663036, by rfl⟩ : syracuseStep 3550715 = 5326073) B5326073
theorem B700059 : Blo 698317 700059 := bstep (se 1 (by rfl) ⟨525044, by rfl⟩ : syracuseStep 700059 = 1050089) B1050089
theorem B798427 : Blo 698317 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B700319 : Blo 698317 700319 := bstep (se 1 (by rfl) ⟨525239, by rfl⟩ : syracuseStep 700319 = 1050479) B1050479
theorem B700443 : Blo 698317 700443 := bstep (se 1 (by rfl) ⟨525332, by rfl⟩ : syracuseStep 700443 = 1050665) B1050665
theorem B700463 : Blo 698317 700463 := bstep (se 1 (by rfl) ⟨525347, by rfl⟩ : syracuseStep 700463 = 1050695) B1050695
theorem B2666591 : Blo 698317 2666591 := bstep (se 1 (by rfl) ⟨1999943, by rfl⟩ : syracuseStep 2666591 = 3999887) B3999887
theorem B700583 : Blo 698317 700583 := bstep (se 1 (by rfl) ⟨525437, by rfl⟩ : syracuseStep 700583 = 1050875) B1050875
theorem B5976251 : Blo 698317 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B19149007 : Blo 698317 19149007 := bstep (se 1 (by rfl) ⟨14361755, by rfl⟩ : syracuseStep 19149007 = 28723511) B28723511
theorem B700719 : Blo 698317 700719 := bstep (se 1 (by rfl) ⟨525539, by rfl⟩ : syracuseStep 700719 = 1051079) B1051079
theorem B700863 : Blo 698317 700863 := bstep (se 1 (by rfl) ⟨525647, by rfl⟩ : syracuseStep 700863 = 1051295) B1051295
theorem B700895 : Blo 698317 700895 := bstep (se 1 (by rfl) ⟨525671, by rfl⟩ : syracuseStep 700895 = 1051343) B1051343
theorem B700959 : Blo 698317 700959 := bstep (se 1 (by rfl) ⟨525719, by rfl⟩ : syracuseStep 700959 = 1051439) B1051439
theorem B701039 : Blo 698317 701039 := bstep (se 1 (by rfl) ⟨525779, by rfl⟩ : syracuseStep 701039 = 1051559) B1051559
theorem B701159 : Blo 698317 701159 := bstep (se 1 (by rfl) ⟨525869, by rfl⟩ : syracuseStep 701159 = 1051739) B1051739
theorem B701211 : Blo 698317 701211 := bstep (se 1 (by rfl) ⟨525908, by rfl⟩ : syracuseStep 701211 = 1051817) B1051817
theorem B2241391 : Blo 698317 2241391 := bstep (se 1 (by rfl) ⟨1681043, by rfl⟩ : syracuseStep 2241391 = 3362087) B3362087
theorem B701487 : Blo 698317 701487 := bstep (se 1 (by rfl) ⟨526115, by rfl⟩ : syracuseStep 701487 = 1052231) B1052231
theorem B701607 : Blo 698317 701607 := bstep (se 1 (by rfl) ⟨526205, by rfl⟩ : syracuseStep 701607 = 1052411) B1052411
theorem B88716545 : Blo 698317 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B701767 : Blo 698317 701767 := bstep (se 1 (by rfl) ⟨526325, by rfl⟩ : syracuseStep 701767 = 1052651) B1052651
theorem B6076217 : Blo 698317 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B18233225 : Blo 698317 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B1259687 : Blo 698317 1259687 := bstep (se 1 (by rfl) ⟨944765, by rfl⟩ : syracuseStep 1259687 = 1889531) B1889531
theorem B2046719 : Blo 698317 2046719 := bstep (se 1 (by rfl) ⟨1535039, by rfl⟩ : syracuseStep 2046719 = 3070079) B3070079
theorem B2702203 : Blo 698317 2702203 := bstep (se 1 (by rfl) ⟨2026652, by rfl⟩ : syracuseStep 2702203 = 4053305) B4053305
theorem B12106867 : Blo 698317 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B3554603 : Blo 698317 3554603 := bstep (se 1 (by rfl) ⟨2665952, by rfl⟩ : syracuseStep 3554603 = 5331905) B5331905
theorem B11517713 : Blo 698317 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B3981251 : Blo 698317 3981251 := bstep (se 1 (by rfl) ⟨2985938, by rfl⟩ : syracuseStep 3981251 = 5971877) B5971877
theorem B49299457 : Blo 698317 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B1327175 : Blo 698317 1327175 := bstep (se 1 (by rfl) ⟨995381, by rfl⟩ : syracuseStep 1327175 = 1990763) B1990763
theorem B43171973 : Blo 698317 43171973 := bstep (se 4 (by rfl) ⟨4047372, by rfl⟩ : syracuseStep 43171973 = 8094745) B8094745
theorem B1491689 : Blo 698317 1491689 := bstep (se 2 (by rfl) ⟨559383, by rfl⟩ : syracuseStep 1491689 = 1118767) B1118767
theorem B5325587 : Blo 698317 5325587 := bstep (se 1 (by rfl) ⟨3994190, by rfl⟩ : syracuseStep 5325587 = 7988381) B7988381
theorem B5981687 : Blo 698317 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B1263095 : Blo 698317 1263095 := bstep (se 1 (by rfl) ⟨947321, by rfl⟩ : syracuseStep 1263095 = 1894643) B1894643
theorem B1329119 : Blo 698317 1329119 := bstep (se 1 (by rfl) ⟨996839, by rfl⟩ : syracuseStep 1329119 = 1993679) B1993679
theorem B1493243 : Blo 698317 1493243 := bstep (se 1 (by rfl) ⟨1119932, by rfl⟩ : syracuseStep 1493243 = 2239865) B2239865
theorem B5983085 : Blo 698317 5983085 := bstep (se 3 (by rfl) ⟨1121828, by rfl⟩ : syracuseStep 5983085 = 2243657) B2243657
theorem B45305345 : Blo 698317 45305345 := bstep (se 2 (by rfl) ⟨16989504, by rfl⟩ : syracuseStep 45305345 = 33979009) B33979009
theorem B1330759 : Blo 698317 1330759 := bstep (se 1 (by rfl) ⟨998069, by rfl⟩ : syracuseStep 1330759 = 1996139) B1996139
theorem B2248681 : Blo 698317 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B10080773 : Blo 698317 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B1495559 : Blo 698317 1495559 := bstep (se 1 (by rfl) ⟨1121669, by rfl⟩ : syracuseStep 1495559 = 2243339) B2243339
theorem B1332217 : Blo 698317 1332217 := bstep (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) B999163
theorem B5329961 : Blo 698317 5329961 := bstep (se 2 (by rfl) ⟨1998735, by rfl⟩ : syracuseStep 5329961 = 3997471) B3997471
theorem B4052663 : Blo 698317 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B1497199 : Blo 698317 1497199 := bstep (se 1 (by rfl) ⟨1122899, by rfl⟩ : syracuseStep 1497199 = 2245799) B2245799
theorem B7985465 : Blo 698317 7985465 := bstep (se 2 (by rfl) ⟨2994549, by rfl⟩ : syracuseStep 7985465 = 5989099) B5989099
theorem B5331419 : Blo 698317 5331419 := bstep (se 1 (by rfl) ⟨3998564, by rfl⟩ : syracuseStep 5331419 = 7997129) B7997129
theorem B20470283 : Blo 698317 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B15129119 : Blo 698317 15129119 := bstep (se 1 (by rfl) ⟨11346839, by rfl⟩ : syracuseStep 15129119 = 22693679) B22693679
theorem B9099985 : Blo 698317 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B5332391 : Blo 698317 5332391 := bstep (se 1 (by rfl) ⟨3999293, by rfl⟩ : syracuseStep 5332391 = 7998587) B7998587
theorem B5400037 : Blo 698317 5400037 := bstep (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) B1012507
theorem B1992539 : Blo 698317 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B8513437 : Blo 698317 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B5041541 : Blo 698317 5041541 := bstep (se 4 (by rfl) ⟨472644, by rfl⟩ : syracuseStep 5041541 = 945289) B945289
theorem B5402011 : Blo 698317 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B1994807 : Blo 698317 1994807 := bstep (se 1 (by rfl) ⟨1496105, by rfl⟩ : syracuseStep 1994807 = 2992211) B2992211
theorem B3994055 : Blo 698317 3994055 := bstep (se 1 (by rfl) ⟨2995541, by rfl⟩ : syracuseStep 3994055 = 5991083) B5991083
theorem B2552813 : Blo 698317 2552813 := bstep (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) B957305
theorem B20771851 : Blo 698317 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B5404967 : Blo 698317 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B5994809 : Blo 698317 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B2652497 : Blo 698317 2652497 := bstep (se 2 (by rfl) ⟨994686, by rfl⟩ : syracuseStep 2652497 = 1989373) B1989373
theorem B12777911 : Blo 698317 12777911 := bstep (se 1 (by rfl) ⟨9583433, by rfl⟩ : syracuseStep 12777911 = 19166867) B19166867
theorem B1768169 : Blo 698317 1768169 := bstep (se 2 (by rfl) ⟨663063, by rfl⟩ : syracuseStep 1768169 = 1326127) B1326127
theorem B1571579 : Blo 698317 1571579 := bstep (se 1 (by rfl) ⟨1178684, by rfl⟩ : syracuseStep 1571579 = 2357369) B2357369
theorem B1571615 : Blo 698317 1571615 := bstep (se 1 (by rfl) ⟨1178711, by rfl⟩ : syracuseStep 1571615 = 2357423) B2357423
theorem B2358071 : Blo 698317 2358071 := bstep (se 1 (by rfl) ⟨1768553, by rfl⟩ : syracuseStep 2358071 = 3537107) B3537107
theorem B2652983 : Blo 698317 2652983 := bstep (se 1 (by rfl) ⟨1989737, by rfl⟩ : syracuseStep 2652983 = 3979475) B3979475
theorem B1178489 : Blo 698317 1178489 := bstep (se 2 (by rfl) ⟨441933, by rfl⟩ : syracuseStep 1178489 = 883867) B883867
theorem B2358503 : Blo 698317 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B785767 : Blo 698317 785767 := bstep (se 1 (by rfl) ⟨589325, by rfl⟩ : syracuseStep 785767 = 1178651) B1178651
theorem B1047911 : Blo 698317 1047911 := bstep (se 1 (by rfl) ⟨785933, by rfl⟩ : syracuseStep 1047911 = 1571867) B1571867
theorem B884191 : Blo 698317 884191 := bstep (se 1 (by rfl) ⟨663143, by rfl⟩ : syracuseStep 884191 = 1326287) B1326287
theorem B1572425 : Blo 698317 1572425 := bstep (se 2 (by rfl) ⟨589659, by rfl⟩ : syracuseStep 1572425 = 1179319) B1179319
theorem B2359151 : Blo 698317 2359151 := bstep (se 1 (by rfl) ⟨1769363, by rfl⟩ : syracuseStep 2359151 = 3538727) B3538727
theorem B65732609 : Blo 698317 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B884783 : Blo 698317 884783 := bstep (se 1 (by rfl) ⟨663587, by rfl⟩ : syracuseStep 884783 = 1327175) B1327175
theorem B1769647 : Blo 698317 1769647 := bstep (se 1 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 1769647 = 2654471) B2654471
theorem B1179967 : Blo 698317 1179967 := bstep (se 1 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 1179967 = 1769951) B1769951
theorem B1049087 : Blo 698317 1049087 := bstep (se 1 (by rfl) ⟨786815, by rfl⟩ : syracuseStep 1049087 = 1573631) B1573631
theorem B786991 : Blo 698317 786991 := bstep (se 1 (by rfl) ⟨590243, by rfl⟩ : syracuseStep 786991 = 1180487) B1180487
theorem B1573595 : Blo 698317 1573595 := bstep (se 1 (by rfl) ⟨1180196, by rfl⟩ : syracuseStep 1573595 = 2360393) B2360393
theorem B1574009 : Blo 698317 1574009 := bstep (se 2 (by rfl) ⟨590253, by rfl⟩ : syracuseStep 1574009 = 1180507) B1180507
theorem B1180831 : Blo 698317 1180831 := bstep (se 1 (by rfl) ⟨885623, by rfl⟩ : syracuseStep 1180831 = 1771247) B1771247
theorem B886079 : Blo 698317 886079 := bstep (se 1 (by rfl) ⟨664559, by rfl⟩ : syracuseStep 886079 = 1329119) B1329119
theorem B8521031 : Blo 698317 8521031 := bstep (se 1 (by rfl) ⟨6390773, by rfl⟩ : syracuseStep 8521031 = 12781547) B12781547
theorem B1574747 : Blo 698317 1574747 := bstep (se 1 (by rfl) ⟨1181060, by rfl⟩ : syracuseStep 1574747 = 2362121) B2362121
theorem B1574891 : Blo 698317 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B1772239 : Blo 698317 1772239 := bstep (se 1 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 1772239 = 2658359) B2658359
theorem B6720515 : Blo 698317 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B1051679 : Blo 698317 1051679 := bstep (se 1 (by rfl) ⟨788759, by rfl⟩ : syracuseStep 1051679 = 1577519) B1577519
theorem B1576007 : Blo 698317 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B109186217 : Blo 698317 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B1052159 : Blo 698317 1052159 := bstep (se 1 (by rfl) ⟨789119, by rfl⟩ : syracuseStep 1052159 = 1578239) B1578239
theorem B790015 : Blo 698317 790015 := bstep (se 1 (by rfl) ⟨592511, by rfl⟩ : syracuseStep 790015 = 1185023) B1185023
theorem B1052297 : Blo 698317 1052297 := bstep (se 2 (by rfl) ⟨394611, by rfl⟩ : syracuseStep 1052297 = 789223) B789223
theorem B5967503 : Blo 698317 5967503 := bstep (se 1 (by rfl) ⟨4475627, by rfl⟩ : syracuseStep 5967503 = 8951255) B8951255
theorem B1052351 : Blo 698317 1052351 := bstep (se 1 (by rfl) ⟨789263, by rfl⟩ : syracuseStep 1052351 = 1578527) B1578527
theorem B3542939 : Blo 698317 3542939 := bstep (se 1 (by rfl) ⟨2657204, by rfl⟩ : syracuseStep 3542939 = 5314409) B5314409
theorem B1577663 : Blo 698317 1577663 := bstep (se 1 (by rfl) ⟨1183247, by rfl⟩ : syracuseStep 1577663 = 2366495) B2366495
theorem B1774345 : Blo 698317 1774345 := bstep (se 2 (by rfl) ⟨665379, by rfl⟩ : syracuseStep 1774345 = 1330759) B1330759
theorem B5313437 : Blo 698317 5313437 := bstep (se 3 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 5313437 = 1992539) B1992539
theorem B1578167 : Blo 698317 1578167 := bstep (se 1 (by rfl) ⟨1183625, by rfl⟩ : syracuseStep 1578167 = 2367251) B2367251
theorem B13473013 : Blo 698317 13473013 := bstep (se 5 (by rfl) ⟨631547, by rfl⟩ : syracuseStep 13473013 = 1263095) B1263095
theorem B25532009 : Blo 698317 25532009 := bstep (se 2 (by rfl) ⟨9574503, by rfl⟩ : syracuseStep 25532009 = 19149007) B19149007
theorem B1578671 : Blo 698317 1578671 := bstep (se 1 (by rfl) ⟨1184003, by rfl⟩ : syracuseStep 1578671 = 2368007) B2368007
theorem B1579283 : Blo 698317 1579283 := bstep (se 1 (by rfl) ⟨1184462, by rfl⟩ : syracuseStep 1579283 = 2368925) B2368925
theorem B1579391 : Blo 698317 1579391 := bstep (se 1 (by rfl) ⟨1184543, by rfl⟩ : syracuseStep 1579391 = 2369087) B2369087
theorem B2988521 : Blo 698317 2988521 := bstep (se 2 (by rfl) ⟨1120695, by rfl⟩ : syracuseStep 2988521 = 2241391) B2241391
theorem B1776289 : Blo 698317 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B27695801 : Blo 698317 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B5315867 : Blo 698317 5315867 := bstep (se 1 (by rfl) ⟨3986900, by rfl⟩ : syracuseStep 5315867 = 7973801) B7973801
theorem B2367143 : Blo 698317 2367143 := bstep (se 1 (by rfl) ⟨1775357, by rfl⟩ : syracuseStep 2367143 = 3550715) B3550715
theorem B57646997 : Blo 698317 57646997 := bstep (se 6 (by rfl) ⟨1351101, by rfl⟩ : syracuseStep 57646997 = 2702203) B2702203
theorem B1777727 : Blo 698317 1777727 := bstep (se 1 (by rfl) ⟨1333295, by rfl⟩ : syracuseStep 1777727 = 2666591) B2666591
theorem B28680317 : Blo 698317 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B2662703 : Blo 698317 2662703 := bstep (se 1 (by rfl) ⟨1997027, by rfl⟩ : syracuseStep 2662703 = 3994055) B3994055
theorem B12133313 : Blo 698317 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B2369735 : Blo 698317 2369735 := bstep (se 1 (by rfl) ⟨1777301, by rfl⟩ : syracuseStep 2369735 = 3554603) B3554603
theorem B698607 : Blo 698317 698607 := bstep (se 1 (by rfl) ⟨523955, by rfl⟩ : syracuseStep 698607 = 1047911) B1047911
theorem B7678475 : Blo 698317 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B28781315 : Blo 698317 28781315 := bstep (se 1 (by rfl) ⟨21585986, by rfl⟩ : syracuseStep 28781315 = 43171973) B43171973
theorem B699163 : Blo 698317 699163 := bstep (se 1 (by rfl) ⟨524372, by rfl⟩ : syracuseStep 699163 = 1048745) B1048745
theorem B699303 : Blo 698317 699303 := bstep (se 1 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 699303 = 1048955) B1048955
theorem B699419 : Blo 698317 699419 := bstep (se 1 (by rfl) ⟨524564, by rfl⟩ : syracuseStep 699419 = 1049129) B1049129
theorem B994459 : Blo 698317 994459 := bstep (se 1 (by rfl) ⟨745844, by rfl⟩ : syracuseStep 994459 = 1491689) B1491689
theorem B3550391 : Blo 698317 3550391 := bstep (se 1 (by rfl) ⟨2662793, by rfl⟩ : syracuseStep 3550391 = 5325587) B5325587
theorem B8105143 : Blo 698317 8105143 := bstep (se 1 (by rfl) ⟨6078857, by rfl⟩ : syracuseStep 8105143 = 12157715) B12157715
theorem B6401213 : Blo 698317 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B699623 : Blo 698317 699623 := bstep (se 1 (by rfl) ⟨524717, by rfl⟩ : syracuseStep 699623 = 1049435) B1049435
theorem B699855 : Blo 698317 699855 := bstep (se 1 (by rfl) ⟨524891, by rfl⟩ : syracuseStep 699855 = 1049783) B1049783
theorem B700015 : Blo 698317 700015 := bstep (se 1 (by rfl) ⟨525011, by rfl⟩ : syracuseStep 700015 = 1050023) B1050023
theorem B700063 : Blo 698317 700063 := bstep (se 1 (by rfl) ⟨525047, by rfl⟩ : syracuseStep 700063 = 1050095) B1050095
theorem B700135 : Blo 698317 700135 := bstep (se 1 (by rfl) ⟨525101, by rfl⟩ : syracuseStep 700135 = 1050203) B1050203
theorem B995495 : Blo 698317 995495 := bstep (se 1 (by rfl) ⟨746621, by rfl⟩ : syracuseStep 995495 = 1493243) B1493243
theorem B700623 : Blo 698317 700623 := bstep (se 1 (by rfl) ⟨525467, by rfl⟩ : syracuseStep 700623 = 1050935) B1050935
theorem B700655 : Blo 698317 700655 := bstep (se 1 (by rfl) ⟨525491, by rfl⟩ : syracuseStep 700655 = 1050983) B1050983
theorem B700743 : Blo 698317 700743 := bstep (se 1 (by rfl) ⟨525557, by rfl⟩ : syracuseStep 700743 = 1051115) B1051115
theorem B700831 : Blo 698317 700831 := bstep (se 1 (by rfl) ⟨525623, by rfl⟩ : syracuseStep 700831 = 1051247) B1051247
theorem B700903 : Blo 698317 700903 := bstep (se 1 (by rfl) ⟨525677, by rfl⟩ : syracuseStep 700903 = 1051355) B1051355
theorem B700911 : Blo 698317 700911 := bstep (se 1 (by rfl) ⟨525683, by rfl⟩ : syracuseStep 700911 = 1051367) B1051367
theorem B3551849 : Blo 698317 3551849 := bstep (se 2 (by rfl) ⟨1331943, by rfl⟩ : syracuseStep 3551849 = 2663887) B2663887
theorem B701467 : Blo 698317 701467 := bstep (se 1 (by rfl) ⟨526100, by rfl⟩ : syracuseStep 701467 = 1052201) B1052201
theorem B11351249 : Blo 698317 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B1455689 : Blo 698317 1455689 := bstep (se 2 (by rfl) ⟨545883, by rfl⟩ : syracuseStep 1455689 = 1091767) B1091767
theorem B997039 : Blo 698317 997039 := bstep (se 1 (by rfl) ⟨747779, by rfl⟩ : syracuseStep 997039 = 1495559) B1495559
theorem B2242313 : Blo 698317 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B3553307 : Blo 698317 3553307 := bstep (se 1 (by rfl) ⟨2664980, by rfl⟩ : syracuseStep 3553307 = 5329961) B5329961
theorem B2996669 : Blo 698317 2996669 := bstep (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) B1123751
theorem B2701775 : Blo 698317 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B5323643 : Blo 698317 5323643 := bstep (se 1 (by rfl) ⟨3992732, by rfl⟩ : syracuseStep 5323643 = 7985465) B7985465
theorem B3554279 : Blo 698317 3554279 := bstep (se 1 (by rfl) ⟨2665709, by rfl⟩ : syracuseStep 3554279 = 5331419) B5331419
theorem B13646855 : Blo 698317 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B3554927 : Blo 698317 3554927 := bstep (se 1 (by rfl) ⟨2666195, by rfl⟩ : syracuseStep 3554927 = 5332391) B5332391
theorem B1064569 : Blo 698317 1064569 := bstep (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) B798427
theorem B2998241 : Blo 698317 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B3981433 : Blo 698317 3981433 := bstep (se 2 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 3981433 = 2986075) B2986075
theorem B6734663 : Blo 698317 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B5686595 : Blo 698317 5686595 := bstep (se 1 (by rfl) ⟨4264946, by rfl⟩ : syracuseStep 5686595 = 8529893) B8529893
theorem B6998057 : Blo 698317 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B3361027 : Blo 698317 3361027 := bstep (se 1 (by rfl) ⟨2520770, by rfl⟩ : syracuseStep 3361027 = 5041541) B5041541
theorem B1329871 : Blo 698317 1329871 := bstep (se 1 (by rfl) ⟨997403, by rfl⟩ : syracuseStep 1329871 = 1994807) B1994807
theorem B3984167 : Blo 698317 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B4050811 : Blo 698317 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B839791 : Blo 698317 839791 := bstep (se 1 (by rfl) ⟨629843, by rfl⟩ : syracuseStep 839791 = 1259687) B1259687
theorem B16142489 : Blo 698317 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B1364479 : Blo 698317 1364479 := bstep (se 1 (by rfl) ⟨1023359, by rfl⟩ : syracuseStep 1364479 = 2046719) B2046719
theorem B3987791 : Blo 698317 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B7559891 : Blo 698317 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B3988723 : Blo 698317 3988723 := bstep (se 1 (by rfl) ⟨2991542, by rfl⟩ : syracuseStep 3988723 = 5983085) B5983085
theorem B7200049 : Blo 698317 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B30203563 : Blo 698317 30203563 := bstep (se 1 (by rfl) ⟨22652672, by rfl⟩ : syracuseStep 30203563 = 45305345) B45305345
theorem B6741737 : Blo 698317 6741737 := bstep (se 2 (by rfl) ⟨2528151, by rfl⟩ : syracuseStep 6741737 = 5056303) B5056303
theorem B1990831 : Blo 698317 1990831 := bstep (se 1 (by rfl) ⟨1493123, by rfl⟩ : syracuseStep 1990831 = 2986247) B2986247
theorem B13460255 : Blo 698317 13460255 := bstep (se 1 (by rfl) ⟨10095191, by rfl⟩ : syracuseStep 13460255 = 20190383) B20190383
theorem B14345405 : Blo 698317 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B1991891 : Blo 698317 1991891 := bstep (se 1 (by rfl) ⟨1493918, by rfl⟩ : syracuseStep 1991891 = 2987837) B2987837
theorem B10086079 : Blo 698317 10086079 := bstep (se 1 (by rfl) ⟨7564559, by rfl⟩ : syracuseStep 10086079 = 15129119) B15129119
theorem B4482803 : Blo 698317 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B7563091 : Blo 698317 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B7202681 : Blo 698317 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B749287 : Blo 698317 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B1995263 : Blo 698317 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B1996265 : Blo 698317 1996265 := bstep (se 2 (by rfl) ⟨748599, by rfl⟩ : syracuseStep 1996265 = 1497199) B1497199
theorem B1701875 : Blo 698317 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B59144363 : Blo 698317 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B12155483 : Blo 698317 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B3603311 : Blo 698317 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B3996539 : Blo 698317 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B1768331 : Blo 698317 1768331 := bstep (se 1 (by rfl) ⟨1326248, by rfl⟩ : syracuseStep 1768331 = 2652497) B2652497
theorem B8518607 : Blo 698317 8518607 := bstep (se 1 (by rfl) ⟨6388955, by rfl⟩ : syracuseStep 8518607 = 12777911) B12777911
theorem B1047689 : Blo 698317 1047689 := bstep (se 2 (by rfl) ⟨392883, by rfl⟩ : syracuseStep 1047689 = 785767) B785767
theorem B1178779 : Blo 698317 1178779 := bstep (se 1 (by rfl) ⟨884084, by rfl⟩ : syracuseStep 1178779 = 1768169) B1768169
theorem B1047719 : Blo 698317 1047719 := bstep (se 1 (by rfl) ⟨785789, by rfl⟩ : syracuseStep 1047719 = 1571579) B1571579
theorem B1047743 : Blo 698317 1047743 := bstep (se 1 (by rfl) ⟨785807, by rfl⟩ : syracuseStep 1047743 = 1571615) B1571615
theorem B1572047 : Blo 698317 1572047 := bstep (se 1 (by rfl) ⟨1179035, by rfl⟩ : syracuseStep 1572047 = 2358071) B2358071
theorem B1768655 : Blo 698317 1768655 := bstep (se 1 (by rfl) ⟨1326491, by rfl⟩ : syracuseStep 1768655 = 2652983) B2652983
theorem B785659 : Blo 698317 785659 := bstep (se 1 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 785659 = 1178489) B1178489
theorem B1178921 : Blo 698317 1178921 := bstep (se 2 (by rfl) ⟨442095, by rfl⟩ : syracuseStep 1178921 = 884191) B884191
theorem B1572335 : Blo 698317 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B1048283 : Blo 698317 1048283 := bstep (se 1 (by rfl) ⟨786212, by rfl⟩ : syracuseStep 1048283 = 1572425) B1572425
theorem B1572767 : Blo 698317 1572767 := bstep (se 1 (by rfl) ⟨1179575, by rfl⟩ : syracuseStep 1572767 = 2359151) B2359151
theorem B2654167 : Blo 698317 2654167 := bstep (se 1 (by rfl) ⟨1990625, by rfl⟩ : syracuseStep 2654167 = 3981251) B3981251
theorem B2359421 : Blo 698317 2359421 := bstep (se 3 (by rfl) ⟨442391, by rfl⟩ : syracuseStep 2359421 = 884783) B884783
theorem B5308577 : Blo 698317 5308577 := bstep (se 2 (by rfl) ⟨1990716, by rfl⟩ : syracuseStep 5308577 = 3981433) B3981433
theorem B2654441 : Blo 698317 2654441 := bstep (se 2 (by rfl) ⟨995415, by rfl⟩ : syracuseStep 2654441 = 1990831) B1990831
theorem B2359529 : Blo 698317 2359529 := bstep (se 2 (by rfl) ⟨884823, by rfl⟩ : syracuseStep 2359529 = 1769647) B1769647
theorem B1573289 : Blo 698317 1573289 := bstep (se 2 (by rfl) ⟨589983, by rfl⟩ : syracuseStep 1573289 = 1179967) B1179967
theorem B2654653 : Blo 698317 2654653 := bstep (se 3 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 2654653 = 995495) B995495
theorem B1049063 : Blo 698317 1049063 := bstep (se 1 (by rfl) ⟨786797, by rfl⟩ : syracuseStep 1049063 = 1573595) B1573595
theorem B4489775 : Blo 698317 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B1049321 : Blo 698317 1049321 := bstep (se 2 (by rfl) ⟨393495, by rfl⟩ : syracuseStep 1049321 = 786991) B786991
theorem B1049339 : Blo 698317 1049339 := bstep (se 1 (by rfl) ⟨787004, by rfl⟩ : syracuseStep 1049339 = 1574009) B1574009
theorem B1049831 : Blo 698317 1049831 := bstep (se 1 (by rfl) ⟨787373, by rfl⟩ : syracuseStep 1049831 = 1574747) B1574747
theorem B1049927 : Blo 698317 1049927 := bstep (se 1 (by rfl) ⟨787445, by rfl⟩ : syracuseStep 1049927 = 1574891) B1574891
theorem B1574441 : Blo 698317 1574441 := bstep (se 2 (by rfl) ⟨590415, by rfl⟩ : syracuseStep 1574441 = 1180831) B1180831
theorem B2656111 : Blo 698317 2656111 := bstep (se 1 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 2656111 = 3984167) B3984167
theorem B1050671 : Blo 698317 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B2361959 : Blo 698317 2361959 := bstep (se 1 (by rfl) ⟨1771469, by rfl⟩ : syracuseStep 2361959 = 3542939) B3542939
theorem B7277221 : Blo 698317 7277221 := bstep (se 4 (by rfl) ⟨682239, by rfl⟩ : syracuseStep 7277221 = 1364479) B1364479
theorem B1051775 : Blo 698317 1051775 := bstep (se 1 (by rfl) ⟨788831, by rfl⟩ : syracuseStep 1051775 = 1577663) B1577663
theorem B3542291 : Blo 698317 3542291 := bstep (se 1 (by rfl) ⟨2656718, by rfl⟩ : syracuseStep 3542291 = 5313437) B5313437
theorem B1052111 : Blo 698317 1052111 := bstep (se 1 (by rfl) ⟨789083, by rfl⟩ : syracuseStep 1052111 = 1578167) B1578167
theorem B2362877 : Blo 698317 2362877 := bstep (se 3 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 2362877 = 886079) B886079
theorem B2362985 : Blo 698317 2362985 := bstep (se 2 (by rfl) ⟨886119, by rfl⟩ : syracuseStep 2362985 = 1772239) B1772239
theorem B1773161 : Blo 698317 1773161 := bstep (se 2 (by rfl) ⟨664935, by rfl⟩ : syracuseStep 1773161 = 1329871) B1329871
theorem B1052447 : Blo 698317 1052447 := bstep (se 1 (by rfl) ⟨789335, by rfl⟩ : syracuseStep 1052447 = 1578671) B1578671
theorem B1052855 : Blo 698317 1052855 := bstep (se 1 (by rfl) ⟨789641, by rfl⟩ : syracuseStep 1052855 = 1579283) B1579283
theorem B2658527 : Blo 698317 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B1052927 : Blo 698317 1052927 := bstep (se 1 (by rfl) ⟨789695, by rfl⟩ : syracuseStep 1052927 = 1579391) B1579391
theorem B1053353 : Blo 698317 1053353 := bstep (se 2 (by rfl) ⟨395007, by rfl⟩ : syracuseStep 1053353 = 790015) B790015
theorem B3543911 : Blo 698317 3543911 := bstep (se 1 (by rfl) ⟨2657933, by rfl⟩ : syracuseStep 3543911 = 5315867) B5315867
theorem B1578095 : Blo 698317 1578095 := bstep (se 1 (by rfl) ⟨1183571, by rfl⟩ : syracuseStep 1578095 = 2367143) B2367143
theorem B4494491 : Blo 698317 4494491 := bstep (se 1 (by rfl) ⟨3370868, by rfl⟩ : syracuseStep 4494491 = 6741737) B6741737
theorem B1185151 : Blo 698317 1185151 := bstep (se 1 (by rfl) ⟨888863, by rfl⟩ : syracuseStep 1185151 = 1777727) B1777727
theorem B1775135 : Blo 698317 1775135 := bstep (se 1 (by rfl) ⟨1331351, by rfl⟩ : syracuseStep 1775135 = 2662703) B2662703
theorem B2365793 : Blo 698317 2365793 := bstep (se 2 (by rfl) ⟨887172, by rfl⟩ : syracuseStep 2365793 = 1774345) B1774345
theorem B1579823 : Blo 698317 1579823 := bstep (se 1 (by rfl) ⟨1184867, by rfl⟩ : syracuseStep 1579823 = 2369735) B2369735
theorem B17964017 : Blo 698317 17964017 := bstep (se 2 (by rfl) ⟨6736506, by rfl⟩ : syracuseStep 17964017 = 13473013) B13473013
theorem B5118983 : Blo 698317 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B2366927 : Blo 698317 2366927 := bstep (se 1 (by rfl) ⟨1775195, by rfl⟩ : syracuseStep 2366927 = 3550391) B3550391
theorem B4267475 : Blo 698317 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B2367899 : Blo 698317 2367899 := bstep (se 1 (by rfl) ⟨1775924, by rfl⟩ : syracuseStep 2367899 = 3551849) B3551849
theorem B2368385 : Blo 698317 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B2368871 : Blo 698317 2368871 := bstep (se 1 (by rfl) ⟨1776653, by rfl⟩ : syracuseStep 2368871 = 3553307) B3553307
theorem B39429575 : Blo 698317 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B5318297 : Blo 698317 5318297 := bstep (se 2 (by rfl) ⟨1994361, by rfl⟩ : syracuseStep 5318297 = 3988723) B3988723
theorem B8103655 : Blo 698317 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B2402207 : Blo 698317 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B3549095 : Blo 698317 3549095 := bstep (se 1 (by rfl) ⟨2661821, by rfl⟩ : syracuseStep 3549095 = 5323643) B5323643
theorem B2664359 : Blo 698317 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B5679071 : Blo 698317 5679071 := bstep (se 1 (by rfl) ⟨4259303, by rfl⟩ : syracuseStep 5679071 = 8518607) B8518607
theorem B2369519 : Blo 698317 2369519 := bstep (se 1 (by rfl) ⟨1777139, by rfl⟩ : syracuseStep 2369519 = 3554279) B3554279
theorem B698459 : Blo 698317 698459 := bstep (se 1 (by rfl) ⟨523844, by rfl⟩ : syracuseStep 698459 = 1047689) B1047689
theorem B698479 : Blo 698317 698479 := bstep (se 1 (by rfl) ⟨523859, by rfl⟩ : syracuseStep 698479 = 1047719) B1047719
theorem B698495 : Blo 698317 698495 := bstep (se 1 (by rfl) ⟨523871, by rfl⟩ : syracuseStep 698495 = 1047743) B1047743
theorem B1419425 : Blo 698317 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B2369951 : Blo 698317 2369951 := bstep (se 1 (by rfl) ⟨1777463, by rfl⟩ : syracuseStep 2369951 = 3554927) B3554927
theorem B698855 : Blo 698317 698855 := bstep (se 1 (by rfl) ⟨524141, by rfl⟩ : syracuseStep 698855 = 1048283) B1048283
theorem B43821739 : Blo 698317 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B699391 : Blo 698317 699391 := bstep (se 1 (by rfl) ⟨524543, by rfl⟩ : syracuseStep 699391 = 1049087) B1049087
theorem B5680687 : Blo 698317 5680687 := bstep (se 1 (by rfl) ⟨4260515, by rfl⟩ : syracuseStep 5680687 = 8521031) B8521031
theorem B4665371 : Blo 698317 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B701119 : Blo 698317 701119 := bstep (se 1 (by rfl) ⟨525839, by rfl⟩ : syracuseStep 701119 = 1051679) B1051679
theorem B72790811 : Blo 698317 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B13448105 : Blo 698317 13448105 := bstep (se 2 (by rfl) ⟨5043039, by rfl⟩ : syracuseStep 13448105 = 10086079) B10086079
theorem B701439 : Blo 698317 701439 := bstep (se 1 (by rfl) ⟨526079, by rfl⟩ : syracuseStep 701439 = 1052159) B1052159
theorem B701531 : Blo 698317 701531 := bstep (se 1 (by rfl) ⟨526148, by rfl⟩ : syracuseStep 701531 = 1052297) B1052297
theorem B3978335 : Blo 698317 3978335 := bstep (se 1 (by rfl) ⟨2983751, by rfl⟩ : syracuseStep 3978335 = 5967503) B5967503
theorem B701567 : Blo 698317 701567 := bstep (se 1 (by rfl) ⟨526175, by rfl⟩ : syracuseStep 701567 = 1052351) B1052351
theorem B10761659 : Blo 698317 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B17021339 : Blo 698317 17021339 := bstep (se 1 (by rfl) ⟨12766004, by rfl⟩ : syracuseStep 17021339 = 25532009) B25532009
theorem B1325945 : Blo 698317 1325945 := bstep (se 2 (by rfl) ⟨497229, by rfl⟩ : syracuseStep 1325945 = 994459) B994459
theorem B999049 : Blo 698317 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B4538333 : Blo 698317 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B19120211 : Blo 698317 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B1327927 : Blo 698317 1327927 := bstep (se 1 (by rfl) ⟨995945, by rfl⟩ : syracuseStep 1327927 = 1991891) B1991891
theorem B4801787 : Blo 698317 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B19187543 : Blo 698317 19187543 := bstep (se 1 (by rfl) ⟨14390657, by rfl⟩ : syracuseStep 19187543 = 28781315) B28781315
theorem B1329385 : Blo 698317 1329385 := bstep (se 2 (by rfl) ⟨498519, by rfl⟩ : syracuseStep 1329385 = 997039) B997039
theorem B1330175 : Blo 698317 1330175 := bstep (se 1 (by rfl) ⟨997631, by rfl⟩ : syracuseStep 1330175 = 1995263) B1995263
theorem B1330843 : Blo 698317 1330843 := bstep (se 1 (by rfl) ⟨998132, by rfl⟩ : syracuseStep 1330843 = 1996265) B1996265
theorem B970459 : Blo 698317 970459 := bstep (se 1 (by rfl) ⟨727844, by rfl⟩ : syracuseStep 970459 = 1455689) B1455689
theorem B1494875 : Blo 698317 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B9097903 : Blo 698317 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B4478885 : Blo 698317 4478885 := bstep (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) B839791
theorem B3791063 : Blo 698317 3791063 := bstep (se 1 (by rfl) ⟨2843297, by rfl⟩ : syracuseStep 3791063 = 5686595) B5686595
theorem B4480343 : Blo 698317 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B10084121 : Blo 698317 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B4481369 : Blo 698317 4481369 := bstep (se 2 (by rfl) ⟨1680513, by rfl⟩ : syracuseStep 4481369 = 3361027) B3361027
theorem B10806857 : Blo 698317 10806857 := bstep (se 2 (by rfl) ⟨4052571, by rfl⟩ : syracuseStep 10806857 = 8105143) B8105143
theorem B1992347 : Blo 698317 1992347 := bstep (se 1 (by rfl) ⟨1494260, by rfl⟩ : syracuseStep 1992347 = 2988521) B2988521
theorem B5039927 : Blo 698317 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B11954141 : Blo 698317 11954141 := bstep (se 3 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 11954141 = 4482803) B4482803
theorem B5401081 : Blo 698317 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B38431331 : Blo 698317 38431331 := bstep (se 1 (by rfl) ⟨28823498, by rfl⟩ : syracuseStep 38431331 = 57646997) B57646997
theorem B8973503 : Blo 698317 8973503 := bstep (se 1 (by rfl) ⟨6730127, by rfl⟩ : syracuseStep 8973503 = 13460255) B13460255
theorem B8088875 : Blo 698317 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B9563603 : Blo 698317 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B73855469 : Blo 698317 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B7567499 : Blo 698317 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B1571705 : Blo 698317 1571705 := bstep (se 2 (by rfl) ⟨589389, by rfl⟩ : syracuseStep 1571705 = 1178779) B1178779
theorem B1997779 : Blo 698317 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B1801183 : Blo 698317 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B1047545 : Blo 698317 1047545 := bstep (se 2 (by rfl) ⟨392829, by rfl⟩ : syracuseStep 1047545 = 785659) B785659
theorem B9600065 : Blo 698317 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B1178887 : Blo 698317 1178887 := bstep (se 1 (by rfl) ⟨884165, by rfl⟩ : syracuseStep 1178887 = 1768331) B1768331
theorem B1048031 : Blo 698317 1048031 := bstep (se 1 (by rfl) ⟨786023, by rfl⟩ : syracuseStep 1048031 = 1572047) B1572047
theorem B1179103 : Blo 698317 1179103 := bstep (se 1 (by rfl) ⟨884327, by rfl⟩ : syracuseStep 1179103 = 1768655) B1768655
theorem B785947 : Blo 698317 785947 := bstep (se 1 (by rfl) ⟨589460, by rfl⟩ : syracuseStep 785947 = 1178921) B1178921
theorem B40271417 : Blo 698317 40271417 := bstep (se 2 (by rfl) ⟨15101781, by rfl⟩ : syracuseStep 40271417 = 30203563) B30203563
theorem B1048223 : Blo 698317 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B1048511 : Blo 698317 1048511 := bstep (se 1 (by rfl) ⟨786383, by rfl⟩ : syracuseStep 1048511 = 1572767) B1572767
theorem B3538889 : Blo 698317 3538889 := bstep (se 2 (by rfl) ⟨1327083, by rfl⟩ : syracuseStep 3538889 = 2654167) B2654167
theorem B1998827 : Blo 698317 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B12746807 : Blo 698317 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B1572947 : Blo 698317 1572947 := bstep (se 1 (by rfl) ⟨1179710, by rfl⟩ : syracuseStep 1572947 = 2359421) B2359421
theorem B3539051 : Blo 698317 3539051 := bstep (se 1 (by rfl) ⟨2654288, by rfl⟩ : syracuseStep 3539051 = 5308577) B5308577
theorem B1769627 : Blo 698317 1769627 := bstep (se 1 (by rfl) ⟨1327220, by rfl⟩ : syracuseStep 1769627 = 2654441) B2654441
theorem B1573019 : Blo 698317 1573019 := bstep (se 1 (by rfl) ⟨1179764, by rfl⟩ : syracuseStep 1573019 = 2359529) B2359529
theorem B1048859 : Blo 698317 1048859 := bstep (se 1 (by rfl) ⟨786644, by rfl⟩ : syracuseStep 1048859 = 1573289) B1573289
theorem B3539537 : Blo 698317 3539537 := bstep (se 2 (by rfl) ⟨1327326, by rfl⟩ : syracuseStep 3539537 = 2654653) B2654653
theorem B1049627 : Blo 698317 1049627 := bstep (se 1 (by rfl) ⟨787220, by rfl⟩ : syracuseStep 1049627 = 1574441) B1574441
theorem B1770569 : Blo 698317 1770569 := bstep (se 2 (by rfl) ⟨663963, by rfl⟩ : syracuseStep 1770569 = 1327927) B1327927
theorem B15140533 : Blo 698317 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B1574639 : Blo 698317 1574639 := bstep (se 1 (by rfl) ⟨1180979, by rfl⟩ : syracuseStep 1574639 = 2361959) B2361959
theorem B886783 : Blo 698317 886783 := bstep (se 1 (by rfl) ⟨665087, by rfl⟩ : syracuseStep 886783 = 1330175) B1330175
theorem B2361527 : Blo 698317 2361527 := bstep (se 1 (by rfl) ⟨1771145, by rfl⟩ : syracuseStep 2361527 = 3542291) B3542291
theorem B1575251 : Blo 698317 1575251 := bstep (se 1 (by rfl) ⟨1181438, by rfl⟩ : syracuseStep 1575251 = 2362877) B2362877
theorem B1575323 : Blo 698317 1575323 := bstep (se 1 (by rfl) ⟨1181492, by rfl⟩ : syracuseStep 1575323 = 2362985) B2362985
theorem B1182107 : Blo 698317 1182107 := bstep (se 1 (by rfl) ⟨886580, by rfl⟩ : syracuseStep 1182107 = 1773161) B1773161
theorem B3541481 : Blo 698317 3541481 := bstep (se 2 (by rfl) ⟨1328055, by rfl⟩ : syracuseStep 3541481 = 2656111) B2656111
theorem B1772351 : Blo 698317 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B1772513 : Blo 698317 1772513 := bstep (se 2 (by rfl) ⟨664692, by rfl⟩ : syracuseStep 1772513 = 1329385) B1329385
theorem B2362607 : Blo 698317 2362607 := bstep (se 1 (by rfl) ⟨1771955, by rfl⟩ : syracuseStep 2362607 = 3543911) B3543911
theorem B1052063 : Blo 698317 1052063 := bstep (se 1 (by rfl) ⟨789047, by rfl⟩ : syracuseStep 1052063 = 1578095) B1578095
theorem B58428985 : Blo 698317 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B1183423 : Blo 698317 1183423 := bstep (se 1 (by rfl) ⟨887567, by rfl⟩ : syracuseStep 1183423 = 1775135) B1775135
theorem B2985923 : Blo 698317 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B2527375 : Blo 698317 2527375 := bstep (se 1 (by rfl) ⟨1895531, by rfl⟩ : syracuseStep 2527375 = 3791063) B3791063
theorem B1577195 : Blo 698317 1577195 := bstep (se 1 (by rfl) ⟨1182896, by rfl⟩ : syracuseStep 1577195 = 2365793) B2365793
theorem B1053215 : Blo 698317 1053215 := bstep (se 1 (by rfl) ⟨789911, by rfl⟩ : syracuseStep 1053215 = 1579823) B1579823
theorem B3412655 : Blo 698317 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B7574249 : Blo 698317 7574249 := bstep (se 2 (by rfl) ⟨2840343, by rfl⟩ : syracuseStep 7574249 = 5680687) B5680687
theorem B1774457 : Blo 698317 1774457 := bstep (se 2 (by rfl) ⟨665421, by rfl⟩ : syracuseStep 1774457 = 1330843) B1330843
theorem B2986895 : Blo 698317 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B1577951 : Blo 698317 1577951 := bstep (se 1 (by rfl) ⟨1183463, by rfl⟩ : syracuseStep 1577951 = 2366927) B2366927
theorem B6722747 : Blo 698317 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B2987579 : Blo 698317 2987579 := bstep (se 1 (by rfl) ⟨2240684, by rfl⟩ : syracuseStep 2987579 = 4481369) B4481369
theorem B1578599 : Blo 698317 1578599 := bstep (se 1 (by rfl) ⟨1183949, by rfl⟩ : syracuseStep 1578599 = 2367899) B2367899
theorem B1578923 : Blo 698317 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B1579247 : Blo 698317 1579247 := bstep (se 1 (by rfl) ⟨1184435, by rfl⟩ : syracuseStep 1579247 = 2368871) B2368871
theorem B26286383 : Blo 698317 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B3545531 : Blo 698317 3545531 := bstep (se 1 (by rfl) ⟨2659148, by rfl⟩ : syracuseStep 3545531 = 5318297) B5318297
theorem B2366063 : Blo 698317 2366063 := bstep (se 1 (by rfl) ⟨1774547, by rfl⟩ : syracuseStep 2366063 = 3549095) B3549095
theorem B1776239 : Blo 698317 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B7969427 : Blo 698317 7969427 := bstep (se 1 (by rfl) ⟨5977070, by rfl⟩ : syracuseStep 7969427 = 11954141) B11954141
theorem B1579679 : Blo 698317 1579679 := bstep (se 1 (by rfl) ⟨1184759, by rfl⟩ : syracuseStep 1579679 = 2369519) B2369519
theorem B1579967 : Blo 698317 1579967 := bstep (se 1 (by rfl) ⟨1184975, by rfl⟩ : syracuseStep 1579967 = 2369951) B2369951
theorem B1580201 : Blo 698317 1580201 := bstep (se 2 (by rfl) ⟨592575, by rfl⟩ : syracuseStep 1580201 = 1185151) B1185151
theorem B25502941 : Blo 698317 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B2663705 : Blo 698317 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B2401577 : Blo 698317 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B11347559 : Blo 698317 11347559 := bstep (se 1 (by rfl) ⟨8510669, by rfl⟩ : syracuseStep 11347559 = 17021339) B17021339
theorem B698363 : Blo 698317 698363 := bstep (se 1 (by rfl) ⟨523772, by rfl⟩ : syracuseStep 698363 = 1047545) B1047545
theorem B6400043 : Blo 698317 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B698687 : Blo 698317 698687 := bstep (se 1 (by rfl) ⟨524015, by rfl⟩ : syracuseStep 698687 = 1048031) B1048031
theorem B26847611 : Blo 698317 26847611 := bstep (se 1 (by rfl) ⟨20135708, by rfl⟩ : syracuseStep 26847611 = 40271417) B40271417
theorem B698815 : Blo 698317 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B699007 : Blo 698317 699007 := bstep (se 1 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 699007 = 1048511) B1048511
theorem B3025555 : Blo 698317 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B699375 : Blo 698317 699375 := bstep (se 1 (by rfl) ⟨524531, by rfl⟩ : syracuseStep 699375 = 1049063) B1049063
theorem B2993183 : Blo 698317 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B699547 : Blo 698317 699547 := bstep (se 1 (by rfl) ⟨524660, by rfl⟩ : syracuseStep 699547 = 1049321) B1049321
theorem B699559 : Blo 698317 699559 := bstep (se 1 (by rfl) ⟨524669, by rfl⟩ : syracuseStep 699559 = 1049339) B1049339
theorem B699887 : Blo 698317 699887 := bstep (se 1 (by rfl) ⟨524915, by rfl⟩ : syracuseStep 699887 = 1049831) B1049831
theorem B699951 : Blo 698317 699951 := bstep (se 1 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 699951 = 1049927) B1049927
theorem B12791695 : Blo 698317 12791695 := bstep (se 1 (by rfl) ⟨9593771, by rfl⟩ : syracuseStep 12791695 = 19187543) B19187543
theorem B700447 : Blo 698317 700447 := bstep (se 1 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 700447 = 1050671) B1050671
theorem B701183 : Blo 698317 701183 := bstep (se 1 (by rfl) ⟨525887, by rfl⟩ : syracuseStep 701183 = 1051775) B1051775
theorem B701407 : Blo 698317 701407 := bstep (se 1 (by rfl) ⟨526055, by rfl⟩ : syracuseStep 701407 = 1052111) B1052111
theorem B701631 : Blo 698317 701631 := bstep (se 1 (by rfl) ⟨526223, by rfl⟩ : syracuseStep 701631 = 1052447) B1052447
theorem B701903 : Blo 698317 701903 := bstep (se 1 (by rfl) ⟨526427, by rfl⟩ : syracuseStep 701903 = 1052855) B1052855
theorem B701951 : Blo 698317 701951 := bstep (se 1 (by rfl) ⟨526463, by rfl⟩ : syracuseStep 701951 = 1052927) B1052927
theorem B702235 : Blo 698317 702235 := bstep (se 1 (by rfl) ⟨526676, by rfl⟩ : syracuseStep 702235 = 1053353) B1053353
theorem B2996327 : Blo 698317 2996327 := bstep (se 1 (by rfl) ⟨2247245, by rfl⟩ : syracuseStep 2996327 = 4494491) B4494491
theorem B38811845 : Blo 698317 38811845 := bstep (se 4 (by rfl) ⟨3638610, by rfl⟩ : syracuseStep 38811845 = 7277221) B7277221
theorem B11976011 : Blo 698317 11976011 := bstep (se 1 (by rfl) ⟨8982008, by rfl⟩ : syracuseStep 11976011 = 17964017) B17964017
theorem B1328231 : Blo 698317 1328231 := bstep (se 1 (by rfl) ⟨996173, by rfl⟩ : syracuseStep 1328231 = 1992347) B1992347
theorem B3359951 : Blo 698317 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B3786047 : Blo 698317 3786047 := bstep (se 1 (by rfl) ⟨2839535, by rfl⟩ : syracuseStep 3786047 = 5679071) B5679071
theorem B5982335 : Blo 698317 5982335 := bstep (se 1 (by rfl) ⟨4486751, by rfl⟩ : syracuseStep 5982335 = 8973503) B8973503
theorem B5392583 : Blo 698317 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B49236979 : Blo 698317 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B8965403 : Blo 698317 8965403 := bstep (se 1 (by rfl) ⟨6724052, by rfl⟩ : syracuseStep 8965403 = 13448105) B13448105
theorem B1332065 : Blo 698317 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B3986333 : Blo 698317 3986333 := bstep (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) B1494875
theorem B1332551 : Blo 698317 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B12440989 : Blo 698317 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B3201191 : Blo 698317 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B7201441 : Blo 698317 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B48522149 : Blo 698317 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B20703125 : Blo 698317 20703125 := bstep (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) B970459
theorem B2844983 : Blo 698317 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B7204571 : Blo 698317 7204571 := bstep (se 1 (by rfl) ⟨5403428, by rfl⟩ : syracuseStep 7204571 = 10806857) B10806857
theorem B1601471 : Blo 698317 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B25620887 : Blo 698317 25620887 := bstep (se 1 (by rfl) ⟨19215665, by rfl⟩ : syracuseStep 25620887 = 38431331) B38431331
theorem B48527207 : Blo 698317 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B2652223 : Blo 698317 2652223 := bstep (se 1 (by rfl) ⟨1989167, by rfl⟩ : syracuseStep 2652223 = 3978335) B3978335
theorem B7174439 : Blo 698317 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B43219493 : Blo 698317 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B5044999 : Blo 698317 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B1571849 : Blo 698317 1571849 := bstep (se 2 (by rfl) ⟨589443, by rfl⟩ : syracuseStep 1571849 = 1178887) B1178887
theorem B883963 : Blo 698317 883963 := bstep (se 1 (by rfl) ⟨662972, by rfl⟩ : syracuseStep 883963 = 1325945) B1325945
theorem B1047803 : Blo 698317 1047803 := bstep (se 1 (by rfl) ⟨785852, by rfl⟩ : syracuseStep 1047803 = 1571705) B1571705
theorem B1572137 : Blo 698317 1572137 := bstep (se 2 (by rfl) ⟨589551, by rfl⟩ : syracuseStep 1572137 = 1179103) B1179103
theorem B1047929 : Blo 698317 1047929 := bstep (se 2 (by rfl) ⟨392973, by rfl⟩ : syracuseStep 1047929 = 785947) B785947
theorem B2359259 : Blo 698317 2359259 := bstep (se 1 (by rfl) ⟨1769444, by rfl⟩ : syracuseStep 2359259 = 3538889) B3538889
theorem B1048631 : Blo 698317 1048631 := bstep (se 1 (by rfl) ⟨786473, by rfl⟩ : syracuseStep 1048631 = 1572947) B1572947
theorem B2359367 : Blo 698317 2359367 := bstep (se 1 (by rfl) ⟨1769525, by rfl⟩ : syracuseStep 2359367 = 3539051) B3539051
theorem B1179751 : Blo 698317 1179751 := bstep (se 1 (by rfl) ⟨884813, by rfl⟩ : syracuseStep 1179751 = 1769627) B1769627
theorem B1048679 : Blo 698317 1048679 := bstep (se 1 (by rfl) ⟨786509, by rfl⟩ : syracuseStep 1048679 = 1573019) B1573019
theorem B2359691 : Blo 698317 2359691 := bstep (se 1 (by rfl) ⟨1769768, by rfl⟩ : syracuseStep 2359691 = 3539537) B3539537
theorem B1180379 : Blo 698317 1180379 := bstep (se 1 (by rfl) ⟨885284, by rfl⟩ : syracuseStep 1180379 = 1770569) B1770569
theorem B885487 : Blo 698317 885487 := bstep (se 1 (by rfl) ⟨664115, by rfl⟩ : syracuseStep 885487 = 1328231) B1328231
theorem B2524031 : Blo 698317 2524031 := bstep (se 1 (by rfl) ⟨1893023, by rfl⟩ : syracuseStep 2524031 = 3786047) B3786047
theorem B9601921 : Blo 698317 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B1049759 : Blo 698317 1049759 := bstep (se 1 (by rfl) ⟨787319, by rfl⟩ : syracuseStep 1049759 = 1574639) B1574639
theorem B1574351 : Blo 698317 1574351 := bstep (se 1 (by rfl) ⟨1180763, by rfl⟩ : syracuseStep 1574351 = 2361527) B2361527
theorem B1050167 : Blo 698317 1050167 := bstep (se 1 (by rfl) ⟨787625, by rfl⟩ : syracuseStep 1050167 = 1575251) B1575251
theorem B1050215 : Blo 698317 1050215 := bstep (se 1 (by rfl) ⟨787661, by rfl⟩ : syracuseStep 1050215 = 1575323) B1575323
theorem B788071 : Blo 698317 788071 := bstep (se 1 (by rfl) ⟨591053, by rfl⟩ : syracuseStep 788071 = 1182107) B1182107
theorem B2360987 : Blo 698317 2360987 := bstep (se 1 (by rfl) ⟨1770740, by rfl⟩ : syracuseStep 2360987 = 3541481) B3541481
theorem B1181567 : Blo 698317 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B1181675 : Blo 698317 1181675 := bstep (se 1 (by rfl) ⟨886256, by rfl⟩ : syracuseStep 1181675 = 1772513) B1772513
theorem B1575071 : Blo 698317 1575071 := bstep (se 1 (by rfl) ⟨1181303, by rfl⟩ : syracuseStep 1575071 = 2362607) B2362607
theorem B20187377 : Blo 698317 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B7965053 : Blo 698317 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B1182377 : Blo 698317 1182377 := bstep (se 2 (by rfl) ⟨443391, by rfl⟩ : syracuseStep 1182377 = 886783) B886783
theorem B1051463 : Blo 698317 1051463 := bstep (se 1 (by rfl) ⟨788597, by rfl⟩ : syracuseStep 1051463 = 1577195) B1577195
theorem B5049499 : Blo 698317 5049499 := bstep (se 1 (by rfl) ⟨3787124, by rfl⟩ : syracuseStep 5049499 = 7574249) B7574249
theorem B1182971 : Blo 698317 1182971 := bstep (se 1 (by rfl) ⟨887228, by rfl⟩ : syracuseStep 1182971 = 1774457) B1774457
theorem B2657555 : Blo 698317 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B1051967 : Blo 698317 1051967 := bstep (se 1 (by rfl) ⟨788975, by rfl⟩ : syracuseStep 1051967 = 1577951) B1577951
theorem B1052399 : Blo 698317 1052399 := bstep (se 1 (by rfl) ⟨789299, by rfl⟩ : syracuseStep 1052399 = 1578599) B1578599
theorem B1052615 : Blo 698317 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B2134127 : Blo 698317 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B1052831 : Blo 698317 1052831 := bstep (se 1 (by rfl) ⟨789623, by rfl⟩ : syracuseStep 1052831 = 1579247) B1579247
theorem B2363687 : Blo 698317 2363687 := bstep (se 1 (by rfl) ⟨1772765, by rfl⟩ : syracuseStep 2363687 = 3545531) B3545531
theorem B1577375 : Blo 698317 1577375 := bstep (se 1 (by rfl) ⟨1183031, by rfl⟩ : syracuseStep 1577375 = 2366063) B2366063
theorem B1184159 : Blo 698317 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B5312951 : Blo 698317 5312951 := bstep (se 1 (by rfl) ⟨3984713, by rfl⟩ : syracuseStep 5312951 = 7969427) B7969427
theorem B1053119 : Blo 698317 1053119 := bstep (se 1 (by rfl) ⟨789839, by rfl⟩ : syracuseStep 1053119 = 1579679) B1579679
theorem B1053311 : Blo 698317 1053311 := bstep (se 1 (by rfl) ⟨789983, by rfl⟩ : syracuseStep 1053311 = 1579967) B1579967
theorem B1053467 : Blo 698317 1053467 := bstep (se 1 (by rfl) ⟨790100, by rfl⟩ : syracuseStep 1053467 = 1580201) B1580201
theorem B1577897 : Blo 698317 1577897 := bstep (se 2 (by rfl) ⟨591711, by rfl⟩ : syracuseStep 1577897 = 1183423) B1183423
theorem B32348099 : Blo 698317 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B1775803 : Blo 698317 1775803 := bstep (se 1 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 1775803 = 2663705) B2663705
theorem B13802083 : Blo 698317 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B4266695 : Blo 698317 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B17898407 : Blo 698317 17898407 := bstep (se 1 (by rfl) ⟨13423805, by rfl⟩ : syracuseStep 17898407 = 26847611) B26847611
theorem B16587985 : Blo 698317 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B17080591 : Blo 698317 17080591 := bstep (se 1 (by rfl) ⟨12810443, by rfl⟩ : syracuseStep 17080591 = 25620887) B25620887
theorem B6726665 : Blo 698317 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B32351471 : Blo 698317 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B28812995 : Blo 698317 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B698535 : Blo 698317 698535 := bstep (se 1 (by rfl) ⟨523901, by rfl⟩ : syracuseStep 698535 = 1047803) B1047803
theorem B698619 : Blo 698317 698619 := bstep (se 1 (by rfl) ⟨523964, by rfl⟩ : syracuseStep 698619 = 1047929) B1047929
theorem B4270589 : Blo 698317 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B8497871 : Blo 698317 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B699239 : Blo 698317 699239 := bstep (se 1 (by rfl) ⟨524429, by rfl⟩ : syracuseStep 699239 = 1048859) B1048859
theorem B699751 : Blo 698317 699751 := bstep (se 1 (by rfl) ⟨524813, by rfl⟩ : syracuseStep 699751 = 1049627) B1049627
theorem B2239967 : Blo 698317 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B5976935 : Blo 698317 5976935 := bstep (se 1 (by rfl) ⟨4482701, by rfl⟩ : syracuseStep 5976935 = 8965403) B8965403
theorem B3552173 : Blo 698317 3552173 := bstep (se 3 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 3552173 = 1332065) B1332065
theorem B701375 : Blo 698317 701375 := bstep (se 1 (by rfl) ⟨526031, by rfl⟩ : syracuseStep 701375 = 1052063) B1052063
theorem B702143 : Blo 698317 702143 := bstep (se 1 (by rfl) ⟨526607, by rfl⟩ : syracuseStep 702143 = 1053215) B1053215
theorem B2275103 : Blo 698317 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B3553469 : Blo 698317 3553469 := bstep (se 3 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 3553469 = 1332551) B1332551
theorem B65649305 : Blo 698317 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B77905313 : Blo 698317 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B17055593 : Blo 698317 17055593 := bstep (se 2 (by rfl) ⟨6395847, by rfl⟩ : syracuseStep 17055593 = 12791695) B12791695
theorem B7586621 : Blo 698317 7586621 := bstep (se 3 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 7586621 = 2844983) B2844983
theorem B4803047 : Blo 698317 4803047 := bstep (se 1 (by rfl) ⟨3602285, by rfl⟩ : syracuseStep 4803047 = 7204571) B7204571
theorem B25874563 : Blo 698317 25874563 := bstep (se 1 (by rfl) ⟨19405922, by rfl⟩ : syracuseStep 25874563 = 38811845) B38811845
theorem B7984007 : Blo 698317 7984007 := bstep (se 1 (by rfl) ⟨5988005, by rfl⟩ : syracuseStep 7984007 = 11976011) B11976011
theorem B3988223 : Blo 698317 3988223 := bstep (se 1 (by rfl) ⟨2991167, by rfl⟩ : syracuseStep 3988223 = 5982335) B5982335
theorem B3595055 : Blo 698317 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B34003921 : Blo 698317 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B1990615 : Blo 698317 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B64545173 : Blo 698317 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B4481831 : Blo 698317 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B1991719 : Blo 698317 1991719 := bstep (se 1 (by rfl) ⟨1493789, by rfl⟩ : syracuseStep 1991719 = 2987579) B2987579
theorem B17524255 : Blo 698317 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B3369833 : Blo 698317 3369833 := bstep (se 2 (by rfl) ⟨1263687, by rfl⟩ : syracuseStep 3369833 = 2527375) B2527375
theorem B1601051 : Blo 698317 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B7565039 : Blo 698317 7565039 := bstep (se 1 (by rfl) ⟨5673779, by rfl⟩ : syracuseStep 7565039 = 11347559) B11347559
theorem B1995455 : Blo 698317 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B3536297 : Blo 698317 3536297 := bstep (se 2 (by rfl) ⟨1326111, by rfl⟩ : syracuseStep 3536297 = 2652223) B2652223
theorem B1997551 : Blo 698317 1997551 := bstep (se 1 (by rfl) ⟨1498163, by rfl⟩ : syracuseStep 1997551 = 2996327) B2996327
theorem B4782959 : Blo 698317 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B1178617 : Blo 698317 1178617 := bstep (se 2 (by rfl) ⟨441981, by rfl⟩ : syracuseStep 1178617 = 883963) B883963
theorem B1047899 : Blo 698317 1047899 := bstep (se 1 (by rfl) ⟨785924, by rfl⟩ : syracuseStep 1047899 = 1571849) B1571849
theorem B1048091 : Blo 698317 1048091 := bstep (se 1 (by rfl) ⟨786068, by rfl⟩ : syracuseStep 1048091 = 1572137) B1572137
theorem B1572839 : Blo 698317 1572839 := bstep (se 1 (by rfl) ⟨1179629, by rfl⟩ : syracuseStep 1572839 = 2359259) B2359259
theorem B1572911 : Blo 698317 1572911 := bstep (se 1 (by rfl) ⟨1179683, by rfl⟩ : syracuseStep 1572911 = 2359367) B2359367
theorem B1573001 : Blo 698317 1573001 := bstep (se 2 (by rfl) ⟨589875, by rfl⟩ : syracuseStep 1573001 = 1179751) B1179751
theorem B1573127 : Blo 698317 1573127 := bstep (se 1 (by rfl) ⟨1179845, by rfl⟩ : syracuseStep 1573127 = 2359691) B2359691
theorem B22774121 : Blo 698317 22774121 := bstep (se 2 (by rfl) ⟨8540295, by rfl⟩ : syracuseStep 22774121 = 17080591) B17080591
theorem B786919 : Blo 698317 786919 := bstep (se 1 (by rfl) ⟨590189, by rfl⟩ : syracuseStep 786919 = 1180379) B1180379
theorem B1049567 : Blo 698317 1049567 := bstep (se 1 (by rfl) ⟨787175, by rfl⟩ : syracuseStep 1049567 = 1574351) B1574351
theorem B1180649 : Blo 698317 1180649 := bstep (se 2 (by rfl) ⟨442743, by rfl⟩ : syracuseStep 1180649 = 885487) B885487
theorem B1573991 : Blo 698317 1573991 := bstep (se 1 (by rfl) ⟨1180493, by rfl⟩ : syracuseStep 1573991 = 2360987) B2360987
theorem B787711 : Blo 698317 787711 := bstep (se 1 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 787711 = 1181567) B1181567
theorem B787783 : Blo 698317 787783 := bstep (se 1 (by rfl) ⟨590837, by rfl⟩ : syracuseStep 787783 = 1181675) B1181675
theorem B2655625 : Blo 698317 2655625 := bstep (se 2 (by rfl) ⟨995859, by rfl⟩ : syracuseStep 2655625 = 1991719) B1991719
theorem B1050047 : Blo 698317 1050047 := bstep (se 1 (by rfl) ⟨787535, by rfl⟩ : syracuseStep 1050047 = 1575071) B1575071
theorem B5310035 : Blo 698317 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B788251 : Blo 698317 788251 := bstep (se 1 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 788251 = 1182377) B1182377
theorem B23365673 : Blo 698317 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B1050761 : Blo 698317 1050761 := bstep (se 2 (by rfl) ⟨394035, by rfl⟩ : syracuseStep 1050761 = 788071) B788071
theorem B788647 : Blo 698317 788647 := bstep (se 1 (by rfl) ⟨591485, by rfl⟩ : syracuseStep 788647 = 1182971) B1182971
theorem B1771703 : Blo 698317 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B1575791 : Blo 698317 1575791 := bstep (se 1 (by rfl) ⟨1181843, by rfl⟩ : syracuseStep 1575791 = 2363687) B2363687
theorem B1051583 : Blo 698317 1051583 := bstep (se 1 (by rfl) ⟨788687, by rfl⟩ : syracuseStep 1051583 = 1577375) B1577375
theorem B789439 : Blo 698317 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B3541967 : Blo 698317 3541967 := bstep (se 1 (by rfl) ⟨2656475, by rfl⟩ : syracuseStep 3541967 = 5312951) B5312951
theorem B1051931 : Blo 698317 1051931 := bstep (se 1 (by rfl) ⟨788948, by rfl⟩ : syracuseStep 1051931 = 1577897) B1577897
theorem B2658815 : Blo 698317 2658815 := bstep (se 1 (by rfl) ⟨1994111, by rfl⟩ : syracuseStep 2658815 = 3988223) B3988223
theorem B11932271 : Blo 698317 11932271 := bstep (se 1 (by rfl) ⟨8949203, by rfl⟩ : syracuseStep 11932271 = 17898407) B17898407
theorem B43030115 : Blo 698317 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B2987887 : Blo 698317 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B21567647 : Blo 698317 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B19208663 : Blo 698317 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B11377853 : Blo 698317 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B2367737 : Blo 698317 2367737 := bstep (se 2 (by rfl) ⟨887901, by rfl⟩ : syracuseStep 2367737 = 1775803) B1775803
theorem B38347253 : Blo 698317 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B2368115 : Blo 698317 2368115 := bstep (se 1 (by rfl) ⟨1776086, by rfl⟩ : syracuseStep 2368115 = 3552173) B3552173
theorem B2663401 : Blo 698317 2663401 := bstep (se 2 (by rfl) ⟨998775, by rfl⟩ : syracuseStep 2663401 = 1997551) B1997551
theorem B1516735 : Blo 698317 1516735 := bstep (se 1 (by rfl) ⟨1137551, by rfl⟩ : syracuseStep 1516735 = 2275103) B2275103
theorem B4269469 : Blo 698317 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B2368979 : Blo 698317 2368979 := bstep (se 1 (by rfl) ⟨1776734, by rfl⟩ : syracuseStep 2368979 = 3553469) B3553469
theorem B3188639 : Blo 698317 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B698599 : Blo 698317 698599 := bstep (se 1 (by rfl) ⟨523949, by rfl⟩ : syracuseStep 698599 = 1047899) B1047899
theorem B698727 : Blo 698317 698727 := bstep (se 1 (by rfl) ⟨524045, by rfl⟩ : syracuseStep 698727 = 1048091) B1048091
theorem B699087 : Blo 698317 699087 := bstep (se 1 (by rfl) ⟨524315, by rfl⟩ : syracuseStep 699087 = 1048631) B1048631
theorem B699119 : Blo 698317 699119 := bstep (se 1 (by rfl) ⟨524339, by rfl⟩ : syracuseStep 699119 = 1048679) B1048679
theorem B5057747 : Blo 698317 5057747 := bstep (se 1 (by rfl) ⟨3793310, by rfl⟩ : syracuseStep 5057747 = 7586621) B7586621
theorem B1682687 : Blo 698317 1682687 := bstep (se 1 (by rfl) ⟨1262015, by rfl⟩ : syracuseStep 1682687 = 2524031) B2524031
theorem B699839 : Blo 698317 699839 := bstep (se 1 (by rfl) ⟨524879, by rfl⟩ : syracuseStep 699839 = 1049759) B1049759
theorem B700111 : Blo 698317 700111 := bstep (se 1 (by rfl) ⟨525083, by rfl⟩ : syracuseStep 700111 = 1050167) B1050167
theorem B700143 : Blo 698317 700143 := bstep (se 1 (by rfl) ⟨525107, by rfl⟩ : syracuseStep 700143 = 1050215) B1050215
theorem B5321213 : Blo 698317 5321213 := bstep (se 3 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 5321213 = 1995455) B1995455
theorem B700975 : Blo 698317 700975 := bstep (se 1 (by rfl) ⟨525731, by rfl⟩ : syracuseStep 700975 = 1051463) B1051463
theorem B701311 : Blo 698317 701311 := bstep (se 1 (by rfl) ⟨525983, by rfl⟩ : syracuseStep 701311 = 1051967) B1051967
theorem B701599 : Blo 698317 701599 := bstep (se 1 (by rfl) ⟨526199, by rfl⟩ : syracuseStep 701599 = 1052399) B1052399
theorem B701743 : Blo 698317 701743 := bstep (se 1 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 701743 = 1052615) B1052615
theorem B17937773 : Blo 698317 17937773 := bstep (se 3 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 17937773 = 6726665) B6726665
theorem B1422751 : Blo 698317 1422751 := bstep (se 1 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 1422751 = 2134127) B2134127
theorem B701887 : Blo 698317 701887 := bstep (se 1 (by rfl) ⟨526415, by rfl⟩ : syracuseStep 701887 = 1052831) B1052831
theorem B702079 : Blo 698317 702079 := bstep (se 1 (by rfl) ⟨526559, by rfl⟩ : syracuseStep 702079 = 1053119) B1053119
theorem B702207 : Blo 698317 702207 := bstep (se 1 (by rfl) ⟨526655, by rfl⟩ : syracuseStep 702207 = 1053311) B1053311
theorem B73611109 : Blo 698317 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B702311 : Blo 698317 702311 := bstep (se 1 (by rfl) ⟨526733, by rfl⟩ : syracuseStep 702311 = 1053467) B1053467
theorem B5322671 : Blo 698317 5322671 := bstep (se 1 (by rfl) ⟨3992003, by rfl⟩ : syracuseStep 5322671 = 7984007) B7984007
theorem B6732665 : Blo 698317 6732665 := bstep (se 2 (by rfl) ⟨2524749, by rfl⟩ : syracuseStep 6732665 = 5049499) B5049499
theorem B86261597 : Blo 698317 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B2246555 : Blo 698317 2246555 := bstep (se 1 (by rfl) ⟨1684916, by rfl⟩ : syracuseStep 2246555 = 3369833) B3369833
theorem B1493311 : Blo 698317 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B3984623 : Blo 698317 3984623 := bstep (se 1 (by rfl) ⟨2988467, by rfl⟩ : syracuseStep 3984623 = 5976935) B5976935
theorem B45338561 : Blo 698317 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B43766203 : Blo 698317 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B13458251 : Blo 698317 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B3202031 : Blo 698317 3202031 := bstep (se 1 (by rfl) ⟨2401523, by rfl⟩ : syracuseStep 3202031 = 4803047) B4803047
theorem B51210245 : Blo 698317 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B34499417 : Blo 698317 34499417 := bstep (se 2 (by rfl) ⟨12937281, by rfl⟩ : syracuseStep 34499417 = 25874563) B25874563
theorem B2847059 : Blo 698317 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B5665247 : Blo 698317 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B5043359 : Blo 698317 5043359 := bstep (se 1 (by rfl) ⟨3782519, by rfl⟩ : syracuseStep 5043359 = 7565039) B7565039
theorem B2357531 : Blo 698317 2357531 := bstep (se 1 (by rfl) ⟨1768148, by rfl⟩ : syracuseStep 2357531 = 3536297) B3536297
theorem B1571489 : Blo 698317 1571489 := bstep (se 2 (by rfl) ⟨589308, by rfl⟩ : syracuseStep 1571489 = 1178617) B1178617
theorem B22117313 : Blo 698317 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B51936875 : Blo 698317 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B11370395 : Blo 698317 11370395 := bstep (se 1 (by rfl) ⟨8527796, by rfl⟩ : syracuseStep 11370395 = 17055593) B17055593
theorem B2654153 : Blo 698317 2654153 := bstep (se 2 (by rfl) ⟨995307, by rfl⟩ : syracuseStep 2654153 = 1990615) B1990615
theorem B1048559 : Blo 698317 1048559 := bstep (se 1 (by rfl) ⟨786419, by rfl⟩ : syracuseStep 1048559 = 1572839) B1572839
theorem B1048607 : Blo 698317 1048607 := bstep (se 1 (by rfl) ⟨786455, by rfl⟩ : syracuseStep 1048607 = 1572911) B1572911
theorem B1048667 : Blo 698317 1048667 := bstep (se 1 (by rfl) ⟨786500, by rfl⟩ : syracuseStep 1048667 = 1573001) B1573001
theorem B1048751 : Blo 698317 1048751 := bstep (se 1 (by rfl) ⟨786563, by rfl⟩ : syracuseStep 1048751 = 1573127) B1573127
theorem B1049225 : Blo 698317 1049225 := bstep (se 2 (by rfl) ⟨393459, by rfl⟩ : syracuseStep 1049225 = 786919) B786919
theorem B787099 : Blo 698317 787099 := bstep (se 1 (by rfl) ⟨590324, by rfl⟩ : syracuseStep 787099 = 1180649) B1180649
theorem B1049327 : Blo 698317 1049327 := bstep (se 1 (by rfl) ⟨786995, by rfl⟩ : syracuseStep 1049327 = 1573991) B1573991
theorem B3540023 : Blo 698317 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B1181135 : Blo 698317 1181135 := bstep (se 1 (by rfl) ⟨885851, by rfl⟩ : syracuseStep 1181135 = 1771703) B1771703
theorem B1050281 : Blo 698317 1050281 := bstep (se 2 (by rfl) ⟨393855, by rfl⟩ : syracuseStep 1050281 = 787711) B787711
theorem B1050377 : Blo 698317 1050377 := bstep (se 2 (by rfl) ⟨393891, by rfl⟩ : syracuseStep 1050377 = 787783) B787783
theorem B3540833 : Blo 698317 3540833 := bstep (se 2 (by rfl) ⟨1327812, by rfl⟩ : syracuseStep 3540833 = 2655625) B2655625
theorem B1050527 : Blo 698317 1050527 := bstep (se 1 (by rfl) ⟨787895, by rfl⟩ : syracuseStep 1050527 = 1575791) B1575791
theorem B2361311 : Blo 698317 2361311 := bstep (se 1 (by rfl) ⟨1770983, by rfl⟩ : syracuseStep 2361311 = 3541967) B3541967
theorem B2656415 : Blo 698317 2656415 := bstep (se 1 (by rfl) ⟨1992311, by rfl⟩ : syracuseStep 2656415 = 3984623) B3984623
theorem B1051001 : Blo 698317 1051001 := bstep (se 2 (by rfl) ⟨394125, by rfl⟩ : syracuseStep 1051001 = 788251) B788251
theorem B1051529 : Blo 698317 1051529 := bstep (se 2 (by rfl) ⟨394323, by rfl⟩ : syracuseStep 1051529 = 788647) B788647
theorem B1772543 : Blo 698317 1772543 := bstep (se 1 (by rfl) ⟨1329407, by rfl⟩ : syracuseStep 1772543 = 2658815) B2658815
theorem B1052585 : Blo 698317 1052585 := bstep (se 2 (by rfl) ⟨394719, by rfl⟩ : syracuseStep 1052585 = 789439) B789439
theorem B2134687 : Blo 698317 2134687 := bstep (se 1 (by rfl) ⟨1601015, by rfl⟩ : syracuseStep 2134687 = 3202031) B3202031
theorem B1578491 : Blo 698317 1578491 := bstep (se 1 (by rfl) ⟨1183868, by rfl⟩ : syracuseStep 1578491 = 2367737) B2367737
theorem B25564835 : Blo 698317 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B1578743 : Blo 698317 1578743 := bstep (se 1 (by rfl) ⟨1184057, by rfl⟩ : syracuseStep 1578743 = 2368115) B2368115
theorem B57513725 : Blo 698317 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B1579319 : Blo 698317 1579319 := bstep (se 1 (by rfl) ⟨1184489, by rfl⟩ : syracuseStep 1579319 = 2368979) B2368979
theorem B1121791 : Blo 698317 1121791 := bstep (se 1 (by rfl) ⟨841343, by rfl⟩ : syracuseStep 1121791 = 1682687) B1682687
theorem B98148145 : Blo 698317 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B3776831 : Blo 698317 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B3547475 : Blo 698317 3547475 := bstep (se 1 (by rfl) ⟨2660606, by rfl⟩ : syracuseStep 3547475 = 5321213) B5321213
theorem B3548447 : Blo 698317 3548447 := bstep (se 1 (by rfl) ⟨2661335, by rfl⟩ : syracuseStep 3548447 = 5322671) B5322671
theorem B7580263 : Blo 698317 7580263 := bstep (se 1 (by rfl) ⟨5685197, by rfl⟩ : syracuseStep 7580263 = 11370395) B11370395
theorem B699039 : Blo 698317 699039 := bstep (se 1 (by rfl) ⟨524279, by rfl⟩ : syracuseStep 699039 = 1048559) B1048559
theorem B15182747 : Blo 698317 15182747 := bstep (se 1 (by rfl) ⟨11387060, by rfl⟩ : syracuseStep 15182747 = 22774121) B22774121
theorem B699711 : Blo 698317 699711 := bstep (se 1 (by rfl) ⟨524783, by rfl⟩ : syracuseStep 699711 = 1049567) B1049567
theorem B700031 : Blo 698317 700031 := bstep (se 1 (by rfl) ⟨525023, by rfl⟩ : syracuseStep 700031 = 1050047) B1050047
theorem B3551201 : Blo 698317 3551201 := bstep (se 2 (by rfl) ⟨1331700, by rfl⟩ : syracuseStep 3551201 = 2663401) B2663401
theorem B15577115 : Blo 698317 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B700507 : Blo 698317 700507 := bstep (se 1 (by rfl) ⟨525380, by rfl⟩ : syracuseStep 700507 = 1050761) B1050761
theorem B701055 : Blo 698317 701055 := bstep (se 1 (by rfl) ⟨525791, by rfl⟩ : syracuseStep 701055 = 1051583) B1051583
theorem B701287 : Blo 698317 701287 := bstep (se 1 (by rfl) ⟨525965, by rfl⟩ : syracuseStep 701287 = 1051931) B1051931
theorem B30225707 : Blo 698317 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B28686743 : Blo 698317 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B7585235 : Blo 698317 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B91998445 : Blo 698317 91998445 := bstep (se 3 (by rfl) ⟨17249708, by rfl⟩ : syracuseStep 91998445 = 34499417) B34499417
theorem B3983849 : Blo 698317 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B3362239 : Blo 698317 3362239 := bstep (se 1 (by rfl) ⟨2521679, by rfl⟩ : syracuseStep 3362239 = 5043359) B5043359
theorem B34624583 : Blo 698317 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B1497703 : Blo 698317 1497703 := bstep (se 1 (by rfl) ⟨1123277, by rfl⟩ : syracuseStep 1497703 = 2246555) B2246555
theorem B5692625 : Blo 698317 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B7954847 : Blo 698317 7954847 := bstep (se 1 (by rfl) ⟨5966135, by rfl⟩ : syracuseStep 7954847 = 11932271) B11932271
theorem B1991081 : Blo 698317 1991081 := bstep (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) B1493311
theorem B12805775 : Blo 698317 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B8972167 : Blo 698317 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B58354937 : Blo 698317 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B8089253 : Blo 698317 8089253 := bstep (se 4 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 8089253 = 1516735) B1516735
theorem B2125759 : Blo 698317 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B34140163 : Blo 698317 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B1897001 : Blo 698317 1897001 := bstep (se 2 (by rfl) ⟨711375, by rfl⟩ : syracuseStep 1897001 = 1422751) B1422751
theorem B3371831 : Blo 698317 3371831 := bstep (se 1 (by rfl) ⟨2528873, by rfl⟩ : syracuseStep 3371831 = 5057747) B5057747
theorem B1898039 : Blo 698317 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B11958515 : Blo 698317 11958515 := bstep (se 1 (by rfl) ⟨8968886, by rfl⟩ : syracuseStep 11958515 = 17937773) B17937773
theorem B1571687 : Blo 698317 1571687 := bstep (se 1 (by rfl) ⟨1178765, by rfl⟩ : syracuseStep 1571687 = 2357531) B2357531
theorem B1047659 : Blo 698317 1047659 := bstep (se 1 (by rfl) ⟨785744, by rfl⟩ : syracuseStep 1047659 = 1571489) B1571489
theorem B4488443 : Blo 698317 4488443 := bstep (se 1 (by rfl) ⟨3366332, by rfl⟩ : syracuseStep 4488443 = 6732665) B6732665
theorem B14744875 : Blo 698317 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B57507731 : Blo 698317 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B1769435 : Blo 698317 1769435 := bstep (se 1 (by rfl) ⟨1327076, by rfl⟩ : syracuseStep 1769435 = 2654153) B2654153
theorem B2360015 : Blo 698317 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B1049465 : Blo 698317 1049465 := bstep (se 2 (by rfl) ⟨393549, by rfl⟩ : syracuseStep 1049465 = 787099) B787099
theorem B787423 : Blo 698317 787423 := bstep (se 1 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 787423 = 1181135) B1181135
theorem B5309549 : Blo 698317 5309549 := bstep (se 3 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 5309549 = 1991081) B1991081
theorem B2360555 : Blo 698317 2360555 := bstep (se 1 (by rfl) ⟨1770416, by rfl⟩ : syracuseStep 2360555 = 3540833) B3540833
theorem B1574207 : Blo 698317 1574207 := bstep (se 1 (by rfl) ⟨1180655, by rfl⟩ : syracuseStep 1574207 = 2361311) B2361311
theorem B1770943 : Blo 698317 1770943 := bstep (se 1 (by rfl) ⟨1328207, by rfl⟩ : syracuseStep 1770943 = 2656415) B2656415
theorem B2655899 : Blo 698317 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1181695 : Blo 698317 1181695 := bstep (se 1 (by rfl) ⟨886271, by rfl⟩ : syracuseStep 1181695 = 1772543) B1772543
theorem B11962889 : Blo 698317 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B1052327 : Blo 698317 1052327 := bstep (se 1 (by rfl) ⟨789245, by rfl⟩ : syracuseStep 1052327 = 1578491) B1578491
theorem B17043223 : Blo 698317 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B1052495 : Blo 698317 1052495 := bstep (se 1 (by rfl) ⟨789371, by rfl⟩ : syracuseStep 1052495 = 1578743) B1578743
theorem B38342483 : Blo 698317 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B1052879 : Blo 698317 1052879 := bstep (se 1 (by rfl) ⟨789659, by rfl⟩ : syracuseStep 1052879 = 1579319) B1579319
theorem B45520217 : Blo 698317 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B2364983 : Blo 698317 2364983 := bstep (se 1 (by rfl) ⟨1773737, by rfl⟩ : syracuseStep 2364983 = 3547475) B3547475
theorem B2365631 : Blo 698317 2365631 := bstep (se 1 (by rfl) ⟨1774223, by rfl⟩ : syracuseStep 2365631 = 3548447) B3548447
theorem B38903291 : Blo 698317 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B2367467 : Blo 698317 2367467 := bstep (se 1 (by rfl) ⟨1775600, by rfl⟩ : syracuseStep 2367467 = 3551201) B3551201
theorem B7972343 : Blo 698317 7972343 := bstep (se 1 (by rfl) ⟨5979257, by rfl⟩ : syracuseStep 7972343 = 11958515) B11958515
theorem B698439 : Blo 698317 698439 := bstep (se 1 (by rfl) ⟨523829, by rfl⟩ : syracuseStep 698439 = 1047659) B1047659
theorem B2992295 : Blo 698317 2992295 := bstep (se 1 (by rfl) ⟨2244221, by rfl⟩ : syracuseStep 2992295 = 4488443) B4488443
theorem B5056823 : Blo 698317 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B699071 : Blo 698317 699071 := bstep (se 1 (by rfl) ⟨524303, by rfl⟩ : syracuseStep 699071 = 1048607) B1048607
theorem B699111 : Blo 698317 699111 := bstep (se 1 (by rfl) ⟨524333, by rfl⟩ : syracuseStep 699111 = 1048667) B1048667
theorem B699167 : Blo 698317 699167 := bstep (se 1 (by rfl) ⟨524375, by rfl⟩ : syracuseStep 699167 = 1048751) B1048751
theorem B699483 : Blo 698317 699483 := bstep (se 1 (by rfl) ⟨524612, by rfl⟩ : syracuseStep 699483 = 1049225) B1049225
theorem B699551 : Blo 698317 699551 := bstep (se 1 (by rfl) ⟨524663, by rfl⟩ : syracuseStep 699551 = 1049327) B1049327
theorem B700187 : Blo 698317 700187 := bstep (se 1 (by rfl) ⟨525140, by rfl⟩ : syracuseStep 700187 = 1050281) B1050281
theorem B700251 : Blo 698317 700251 := bstep (se 1 (by rfl) ⟨525188, by rfl⟩ : syracuseStep 700251 = 1050377) B1050377
theorem B700351 : Blo 698317 700351 := bstep (se 1 (by rfl) ⟨525263, by rfl⟩ : syracuseStep 700351 = 1050527) B1050527
theorem B700667 : Blo 698317 700667 := bstep (se 1 (by rfl) ⟨525500, by rfl⟩ : syracuseStep 700667 = 1051001) B1051001
theorem B701019 : Blo 698317 701019 := bstep (se 1 (by rfl) ⟨525764, by rfl⟩ : syracuseStep 701019 = 1051529) B1051529
theorem B701723 : Blo 698317 701723 := bstep (se 1 (by rfl) ⟨526292, by rfl⟩ : syracuseStep 701723 = 1052585) B1052585
theorem B122664593 : Blo 698317 122664593 := bstep (se 2 (by rfl) ⟨45999222, by rfl⟩ : syracuseStep 122664593 = 91998445) B91998445
theorem B23083055 : Blo 698317 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B10107017 : Blo 698317 10107017 := bstep (se 2 (by rfl) ⟨3790131, by rfl⟩ : syracuseStep 10107017 = 7580263) B7580263
theorem B5061437 : Blo 698317 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B2834345 : Blo 698317 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B8537183 : Blo 698317 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B5392835 : Blo 698317 5392835 := bstep (se 1 (by rfl) ⟨4044626, by rfl⟩ : syracuseStep 5392835 = 8089253) B8089253
theorem B1264667 : Blo 698317 1264667 := bstep (se 1 (by rfl) ⟨948500, by rfl⟩ : syracuseStep 1264667 = 1897001) B1897001
theorem B2247887 : Blo 698317 2247887 := bstep (se 1 (by rfl) ⟨1685915, by rfl⟩ : syracuseStep 2247887 = 3371831) B3371831
theorem B19124495 : Blo 698317 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B1495721 : Blo 698317 1495721 := bstep (se 2 (by rfl) ⟨560895, by rfl⟩ : syracuseStep 1495721 = 1121791) B1121791
theorem B130864193 : Blo 698317 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B41538973 : Blo 698317 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B4482985 : Blo 698317 4482985 := bstep (se 2 (by rfl) ⟨1681119, by rfl⟩ : syracuseStep 4482985 = 3362239) B3362239
theorem B3795083 : Blo 698317 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B2517887 : Blo 698317 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B5303231 : Blo 698317 5303231 := bstep (se 1 (by rfl) ⟨3977423, by rfl⟩ : syracuseStep 5303231 = 7954847) B7954847
theorem B2846249 : Blo 698317 2846249 := bstep (se 2 (by rfl) ⟨1067343, by rfl⟩ : syracuseStep 2846249 = 2134687) B2134687
theorem B10121831 : Blo 698317 10121831 := bstep (se 1 (by rfl) ⟨7591373, by rfl⟩ : syracuseStep 10121831 = 15182747) B15182747
theorem B1996937 : Blo 698317 1996937 := bstep (se 2 (by rfl) ⟨748851, by rfl⟩ : syracuseStep 1996937 = 1497703) B1497703
theorem B20150471 : Blo 698317 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B19659833 : Blo 698317 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B1047791 : Blo 698317 1047791 := bstep (se 1 (by rfl) ⟨785843, by rfl⟩ : syracuseStep 1047791 = 1571687) B1571687
theorem B38338487 : Blo 698317 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B1179623 : Blo 698317 1179623 := bstep (se 1 (by rfl) ⟨884717, by rfl⟩ : syracuseStep 1179623 = 1769435) B1769435
theorem B1573343 : Blo 698317 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B3539699 : Blo 698317 3539699 := bstep (se 1 (by rfl) ⟨2654774, by rfl⟩ : syracuseStep 3539699 = 5309549) B5309549
theorem B1573703 : Blo 698317 1573703 := bstep (se 1 (by rfl) ⟨1180277, by rfl⟩ : syracuseStep 1573703 = 2360555) B2360555
theorem B1049471 : Blo 698317 1049471 := bstep (se 1 (by rfl) ⟨787103, by rfl⟩ : syracuseStep 1049471 = 1574207) B1574207
theorem B1770599 : Blo 698317 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B1049897 : Blo 698317 1049897 := bstep (se 2 (by rfl) ⟨393711, by rfl⟩ : syracuseStep 1049897 = 787423) B787423
theorem B2361257 : Blo 698317 2361257 := bstep (se 2 (by rfl) ⟨885471, by rfl⟩ : syracuseStep 2361257 = 1770943) B1770943
theorem B25561655 : Blo 698317 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B1575593 : Blo 698317 1575593 := bstep (se 2 (by rfl) ⟨590847, by rfl⟩ : syracuseStep 1575593 = 1181695) B1181695
theorem B12749663 : Blo 698317 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B30346811 : Blo 698317 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B1576655 : Blo 698317 1576655 := bstep (se 1 (by rfl) ⟨1182491, by rfl⟩ : syracuseStep 1576655 = 2364983) B2364983
theorem B1577087 : Blo 698317 1577087 := bstep (se 1 (by rfl) ⟨1182815, by rfl⟩ : syracuseStep 1577087 = 2365631) B2365631
theorem B1578311 : Blo 698317 1578311 := bstep (se 1 (by rfl) ⟨1183733, by rfl⟩ : syracuseStep 1578311 = 2367467) B2367467
theorem B5314895 : Blo 698317 5314895 := bstep (se 1 (by rfl) ⟨3986171, by rfl⟩ : syracuseStep 5314895 = 7972343) B7972343
theorem B2530055 : Blo 698317 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B55385297 : Blo 698317 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B1678591 : Blo 698317 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B698527 : Blo 698317 698527 := bstep (se 1 (by rfl) ⟨523895, by rfl⟩ : syracuseStep 698527 = 1047791) B1047791
theorem B699643 : Blo 698317 699643 := bstep (se 1 (by rfl) ⟨524732, by rfl⟩ : syracuseStep 699643 = 1049465) B1049465
theorem B7975259 : Blo 698317 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B701551 : Blo 698317 701551 := bstep (se 1 (by rfl) ⟨526163, by rfl⟩ : syracuseStep 701551 = 1052327) B1052327
theorem B701663 : Blo 698317 701663 := bstep (se 1 (by rfl) ⟨526247, by rfl⟩ : syracuseStep 701663 = 1052495) B1052495
theorem B5977313 : Blo 698317 5977313 := bstep (se 2 (by rfl) ⟨2241492, by rfl⟩ : syracuseStep 5977313 = 4482985) B4482985
theorem B701919 : Blo 698317 701919 := bstep (se 1 (by rfl) ⟨526439, by rfl⟩ : syracuseStep 701919 = 1052879) B1052879
theorem B997147 : Blo 698317 997147 := bstep (se 1 (by rfl) ⟨747860, by rfl⟩ : syracuseStep 997147 = 1495721) B1495721
theorem B87242795 : Blo 698317 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B25935527 : Blo 698317 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B22724297 : Blo 698317 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B81776395 : Blo 698317 81776395 := bstep (se 1 (by rfl) ⟨61332296, by rfl⟩ : syracuseStep 81776395 = 122664593) B122664593
theorem B15388703 : Blo 698317 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B6738011 : Blo 698317 6738011 := bstep (se 1 (by rfl) ⟨5053508, by rfl⟩ : syracuseStep 6738011 = 10107017) B10107017
theorem B1331291 : Blo 698317 1331291 := bstep (se 1 (by rfl) ⟨998468, by rfl⟩ : syracuseStep 1331291 = 1996937) B1996937
theorem B1889563 : Blo 698317 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B5691455 : Blo 698317 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B3595223 : Blo 698317 3595223 := bstep (se 1 (by rfl) ⟨2696417, by rfl⟩ : syracuseStep 3595223 = 5392835) B5392835
theorem B1498591 : Blo 698317 1498591 := bstep (se 1 (by rfl) ⟨1123943, by rfl⟩ : syracuseStep 1498591 = 2247887) B2247887
theorem B1994863 : Blo 698317 1994863 := bstep (se 1 (by rfl) ⟨1496147, by rfl⟩ : syracuseStep 1994863 = 2992295) B2992295
theorem B3371215 : Blo 698317 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B3535487 : Blo 698317 3535487 := bstep (se 1 (by rfl) ⟨2651615, by rfl⟩ : syracuseStep 3535487 = 5303231) B5303231
theorem B1897499 : Blo 698317 1897499 := bstep (se 1 (by rfl) ⟨1423124, by rfl⟩ : syracuseStep 1897499 = 2846249) B2846249
theorem B3372445 : Blo 698317 3372445 := bstep (se 3 (by rfl) ⟨632333, by rfl⟩ : syracuseStep 3372445 = 1264667) B1264667
theorem B6747887 : Blo 698317 6747887 := bstep (se 1 (by rfl) ⟨5060915, by rfl⟩ : syracuseStep 6747887 = 10121831) B10121831
theorem B13433647 : Blo 698317 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B3374291 : Blo 698317 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B13106555 : Blo 698317 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B25558991 : Blo 698317 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B786415 : Blo 698317 786415 := bstep (se 1 (by rfl) ⟨589811, by rfl⟩ : syracuseStep 786415 = 1179623) B1179623
theorem B1048895 : Blo 698317 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B2359799 : Blo 698317 2359799 := bstep (se 1 (by rfl) ⟨1769849, by rfl⟩ : syracuseStep 2359799 = 3539699) B3539699
theorem B1049135 : Blo 698317 1049135 := bstep (se 1 (by rfl) ⟨786851, by rfl⟩ : syracuseStep 1049135 = 1573703) B1573703
theorem B1180399 : Blo 698317 1180399 := bstep (se 1 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 1180399 = 1770599) B1770599
theorem B1574171 : Blo 698317 1574171 := bstep (se 1 (by rfl) ⟨1180628, by rfl⟩ : syracuseStep 1574171 = 2361257) B2361257
theorem B17041103 : Blo 698317 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B1050395 : Blo 698317 1050395 := bstep (se 1 (by rfl) ⟨787796, by rfl⟩ : syracuseStep 1050395 = 1575593) B1575593
theorem B1051103 : Blo 698317 1051103 := bstep (se 1 (by rfl) ⟨788327, by rfl⟩ : syracuseStep 1051103 = 1576655) B1576655
theorem B10259135 : Blo 698317 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B4492007 : Blo 698317 4492007 := bstep (se 1 (by rfl) ⟨3369005, by rfl⟩ : syracuseStep 4492007 = 6738011) B6738011
theorem B887527 : Blo 698317 887527 := bstep (se 1 (by rfl) ⟨665645, by rfl⟩ : syracuseStep 887527 = 1331291) B1331291
theorem B1051391 : Blo 698317 1051391 := bstep (se 1 (by rfl) ⟨788543, by rfl⟩ : syracuseStep 1051391 = 1577087) B1577087
theorem B1052207 : Blo 698317 1052207 := bstep (se 1 (by rfl) ⟨789155, by rfl⟩ : syracuseStep 1052207 = 1578311) B1578311
theorem B3543263 : Blo 698317 3543263 := bstep (se 1 (by rfl) ⟨2657447, by rfl⟩ : syracuseStep 3543263 = 5314895) B5314895
theorem B2659817 : Blo 698317 2659817 := bstep (se 2 (by rfl) ⟨997431, by rfl⟩ : syracuseStep 2659817 = 1994863) B1994863
theorem B4494953 : Blo 698317 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B4496593 : Blo 698317 4496593 := bstep (se 2 (by rfl) ⟨1686222, by rfl⟩ : syracuseStep 4496593 = 3372445) B3372445
theorem B5316839 : Blo 698317 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B4498591 : Blo 698317 4498591 := bstep (se 1 (by rfl) ⟨3373943, by rfl⟩ : syracuseStep 4498591 = 6747887) B6747887
theorem B2238121 : Blo 698317 2238121 := bstep (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) B1678591
theorem B15149531 : Blo 698317 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B699647 : Blo 698317 699647 := bstep (se 1 (by rfl) ⟨524735, by rfl⟩ : syracuseStep 699647 = 1049471) B1049471
theorem B699931 : Blo 698317 699931 := bstep (se 1 (by rfl) ⟨524948, by rfl⟩ : syracuseStep 699931 = 1049897) B1049897
theorem B8499775 : Blo 698317 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B20231207 : Blo 698317 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B109035193 : Blo 698317 109035193 := bstep (se 2 (by rfl) ⟨40888197, by rfl⟩ : syracuseStep 109035193 = 81776395) B81776395
theorem B1329529 : Blo 698317 1329529 := bstep (se 2 (by rfl) ⟨498573, by rfl⟩ : syracuseStep 1329529 = 997147) B997147
theorem B9587261 : Blo 698317 9587261 := bstep (se 3 (by rfl) ⟨1797611, by rfl⟩ : syracuseStep 9587261 = 3595223) B3595223
theorem B1264999 : Blo 698317 1264999 := bstep (se 1 (by rfl) ⟨948749, by rfl⟩ : syracuseStep 1264999 = 1897499) B1897499
theorem B3984875 : Blo 698317 3984875 := bstep (se 1 (by rfl) ⟨2988656, by rfl⟩ : syracuseStep 3984875 = 5977313) B5977313
theorem B17911529 : Blo 698317 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B2249527 : Blo 698317 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B8737703 : Blo 698317 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B17290351 : Blo 698317 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B3794303 : Blo 698317 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B36923531 : Blo 698317 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B2519417 : Blo 698317 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B6746813 : Blo 698317 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B2356991 : Blo 698317 2356991 := bstep (se 1 (by rfl) ⟨1767743, by rfl⟩ : syracuseStep 2356991 = 3535487) B3535487
theorem B58161863 : Blo 698317 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B1998121 : Blo 698317 1998121 := bstep (se 2 (by rfl) ⟨749295, by rfl⟩ : syracuseStep 1998121 = 1498591) B1498591
theorem B17039327 : Blo 698317 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B1048553 : Blo 698317 1048553 := bstep (se 2 (by rfl) ⟨393207, by rfl⟩ : syracuseStep 1048553 = 786415) B786415
theorem B1573199 : Blo 698317 1573199 := bstep (se 1 (by rfl) ⟨1179899, by rfl⟩ : syracuseStep 1573199 = 2359799) B2359799
theorem B1049447 : Blo 698317 1049447 := bstep (se 1 (by rfl) ⟨787085, by rfl⟩ : syracuseStep 1049447 = 1574171) B1574171
theorem B1573865 : Blo 698317 1573865 := bstep (se 2 (by rfl) ⟨590199, by rfl⟩ : syracuseStep 1573865 = 1180399) B1180399
theorem B5998121 : Blo 698317 5998121 := bstep (se 2 (by rfl) ⟨2249295, by rfl⟩ : syracuseStep 5998121 = 4498591) B4498591
theorem B6391507 : Blo 698317 6391507 := bstep (se 1 (by rfl) ⟨4793630, by rfl⟩ : syracuseStep 6391507 = 9587261) B9587261
theorem B2656583 : Blo 698317 2656583 := bstep (se 1 (by rfl) ⟨1992437, by rfl⟩ : syracuseStep 2656583 = 3984875) B3984875
theorem B2362175 : Blo 698317 2362175 := bstep (se 1 (by rfl) ⟨1771631, by rfl⟩ : syracuseStep 2362175 = 3543263) B3543263
theorem B1772705 : Blo 698317 1772705 := bstep (se 2 (by rfl) ⟨664764, by rfl⟩ : syracuseStep 1772705 = 1329529) B1329529
theorem B1183369 : Blo 698317 1183369 := bstep (se 2 (by rfl) ⟨443763, by rfl⟩ : syracuseStep 1183369 = 887527) B887527
theorem B1773211 : Blo 698317 1773211 := bstep (se 1 (by rfl) ⟨1329908, by rfl⟩ : syracuseStep 1773211 = 2659817) B2659817
theorem B3544559 : Blo 698317 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B92215205 : Blo 698317 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B10099687 : Blo 698317 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B1679611 : Blo 698317 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B4497875 : Blo 698317 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B11936645 : Blo 698317 11936645 := bstep (se 4 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 11936645 = 2238121) B2238121
theorem B2664161 : Blo 698317 2664161 := bstep (se 2 (by rfl) ⟨999060, by rfl⟩ : syracuseStep 2664161 = 1998121) B1998121
theorem B38774575 : Blo 698317 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B699035 : Blo 698317 699035 := bstep (se 1 (by rfl) ⟨524276, by rfl⟩ : syracuseStep 699035 = 1048553) B1048553
theorem B699263 : Blo 698317 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B699423 : Blo 698317 699423 := bstep (se 1 (by rfl) ⟨524567, by rfl⟩ : syracuseStep 699423 = 1049135) B1049135
theorem B700263 : Blo 698317 700263 := bstep (se 1 (by rfl) ⟨525197, by rfl⟩ : syracuseStep 700263 = 1050395) B1050395
theorem B700735 : Blo 698317 700735 := bstep (se 1 (by rfl) ⟨525551, by rfl⟩ : syracuseStep 700735 = 1051103) B1051103
theorem B2994671 : Blo 698317 2994671 := bstep (se 1 (by rfl) ⟨2246003, by rfl⟩ : syracuseStep 2994671 = 4492007) B4492007
theorem B700927 : Blo 698317 700927 := bstep (se 1 (by rfl) ⟨525695, by rfl⟩ : syracuseStep 700927 = 1051391) B1051391
theorem B701471 : Blo 698317 701471 := bstep (se 1 (by rfl) ⟨526103, by rfl⟩ : syracuseStep 701471 = 1052207) B1052207
theorem B11941019 : Blo 698317 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B2996635 : Blo 698317 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B1686665 : Blo 698317 1686665 := bstep (se 2 (by rfl) ⟨632499, by rfl⟩ : syracuseStep 1686665 = 1264999) B1264999
theorem B2999369 : Blo 698317 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B13487471 : Blo 698317 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B145380257 : Blo 698317 145380257 := bstep (se 2 (by rfl) ⟨54517596, by rfl⟩ : syracuseStep 145380257 = 109035193) B109035193
theorem B45438205 : Blo 698317 45438205 := bstep (se 3 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 45438205 = 17039327) B17039327
theorem B11360735 : Blo 698317 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B6839423 : Blo 698317 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B5825135 : Blo 698317 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B10118141 : Blo 698317 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B98462749 : Blo 698317 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B11333033 : Blo 698317 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B1571327 : Blo 698317 1571327 := bstep (se 1 (by rfl) ⟨1178495, by rfl⟩ : syracuseStep 1571327 = 2356991) B2356991
theorem B5995457 : Blo 698317 5995457 := bstep (se 2 (by rfl) ⟨2248296, by rfl⟩ : syracuseStep 5995457 = 4496593) B4496593
theorem B1048799 : Blo 698317 1048799 := bstep (se 1 (by rfl) ⟨786599, by rfl⟩ : syracuseStep 1048799 = 1573199) B1573199
theorem B1049243 : Blo 698317 1049243 := bstep (se 1 (by rfl) ⟨786932, by rfl⟩ : syracuseStep 1049243 = 1573865) B1573865
theorem B1999579 : Blo 698317 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B3998747 : Blo 698317 3998747 := bstep (se 1 (by rfl) ⟨2999060, by rfl⟩ : syracuseStep 3998747 = 5998121) B5998121
theorem B1771055 : Blo 698317 1771055 := bstep (se 1 (by rfl) ⟨1328291, by rfl⟩ : syracuseStep 1771055 = 2656583) B2656583
theorem B15533693 : Blo 698317 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B1574783 : Blo 698317 1574783 := bstep (se 1 (by rfl) ⟨1181087, by rfl⟩ : syracuseStep 1574783 = 2362175) B2362175
theorem B1181803 : Blo 698317 1181803 := bstep (se 1 (by rfl) ⟨886352, by rfl⟩ : syracuseStep 1181803 = 1772705) B1772705
theorem B8522009 : Blo 698317 8522009 := bstep (se 2 (by rfl) ⟨3195753, by rfl⟩ : syracuseStep 8522009 = 6391507) B6391507
theorem B2363039 : Blo 698317 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B61476803 : Blo 698317 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B7573823 : Blo 698317 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B4559615 : Blo 698317 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B1577825 : Blo 698317 1577825 := bstep (se 2 (by rfl) ⟨591684, by rfl⟩ : syracuseStep 1577825 = 1183369) B1183369
theorem B2364281 : Blo 698317 2364281 := bstep (se 2 (by rfl) ⟨886605, by rfl⟩ : syracuseStep 2364281 = 1773211) B1773211
theorem B1776107 : Blo 698317 1776107 := bstep (se 1 (by rfl) ⟨1332080, by rfl⟩ : syracuseStep 1776107 = 2664161) B2664161
theorem B1124443 : Blo 698317 1124443 := bstep (se 1 (by rfl) ⟨843332, by rfl⟩ : syracuseStep 1124443 = 1686665) B1686665
theorem B2239481 : Blo 698317 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B699631 : Blo 698317 699631 := bstep (se 1 (by rfl) ⟨524723, by rfl⟩ : syracuseStep 699631 = 1049447) B1049447
theorem B8991647 : Blo 698317 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B131283665 : Blo 698317 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B2998583 : Blo 698317 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B7555355 : Blo 698317 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B51699433 : Blo 698317 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B96920171 : Blo 698317 96920171 := bstep (se 1 (by rfl) ⟨72690128, by rfl⟩ : syracuseStep 96920171 = 145380257) B145380257
theorem B7957763 : Blo 698317 7957763 := bstep (se 1 (by rfl) ⟨5968322, by rfl⟩ : syracuseStep 7957763 = 11936645) B11936645
theorem B6745427 : Blo 698317 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B60584273 : Blo 698317 60584273 := bstep (se 2 (by rfl) ⟨22719102, by rfl⟩ : syracuseStep 60584273 = 45438205) B45438205
theorem B1996447 : Blo 698317 1996447 := bstep (se 1 (by rfl) ⟨1497335, by rfl⟩ : syracuseStep 1996447 = 2994671) B2994671
theorem B3995513 : Blo 698317 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B7960679 : Blo 698317 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B13466249 : Blo 698317 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B1047551 : Blo 698317 1047551 := bstep (se 1 (by rfl) ⟨785663, by rfl⟩ : syracuseStep 1047551 = 1571327) B1571327
theorem B3996971 : Blo 698317 3996971 := bstep (se 1 (by rfl) ⟨2997728, by rfl⟩ : syracuseStep 3996971 = 5995457) B5995457
theorem B1999055 : Blo 698317 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B1180703 : Blo 698317 1180703 := bstep (se 1 (by rfl) ⟨885527, by rfl⟩ : syracuseStep 1180703 = 1771055) B1771055
theorem B10355795 : Blo 698317 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B1049855 : Blo 698317 1049855 := bstep (se 1 (by rfl) ⟨787391, by rfl⟩ : syracuseStep 1049855 = 1574783) B1574783
theorem B1575359 : Blo 698317 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B1575737 : Blo 698317 1575737 := bstep (se 2 (by rfl) ⟨590901, by rfl⟩ : syracuseStep 1575737 = 1181803) B1181803
theorem B5049215 : Blo 698317 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B1051883 : Blo 698317 1051883 := bstep (se 1 (by rfl) ⟨788912, by rfl⟩ : syracuseStep 1051883 = 1577825) B1577825
theorem B1576187 : Blo 698317 1576187 := bstep (se 1 (by rfl) ⟨1182140, by rfl⟩ : syracuseStep 1576187 = 2364281) B2364281
theorem B1184071 : Blo 698317 1184071 := bstep (se 1 (by rfl) ⟨888053, by rfl⟩ : syracuseStep 1184071 = 1776107) B1776107
theorem B2661929 : Blo 698317 2661929 := bstep (se 2 (by rfl) ⟨998223, by rfl⟩ : syracuseStep 2661929 = 1996447) B1996447
theorem B4496951 : Blo 698317 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B2663675 : Blo 698317 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B698367 : Blo 698317 698367 := bstep (se 1 (by rfl) ⟨523775, by rfl⟩ : syracuseStep 698367 = 1047551) B1047551
theorem B2664647 : Blo 698317 2664647 := bstep (se 1 (by rfl) ⟨1998485, by rfl⟩ : syracuseStep 2664647 = 3996971) B3996971
theorem B699199 : Blo 698317 699199 := bstep (se 1 (by rfl) ⟨524399, by rfl⟩ : syracuseStep 699199 = 1048799) B1048799
theorem B699495 : Blo 698317 699495 := bstep (se 1 (by rfl) ⟨524621, by rfl⟩ : syracuseStep 699495 = 1049243) B1049243
theorem B2665831 : Blo 698317 2665831 := bstep (se 1 (by rfl) ⟨1999373, by rfl⟩ : syracuseStep 2665831 = 3998747) B3998747
theorem B2666105 : Blo 698317 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B5681339 : Blo 698317 5681339 := bstep (se 1 (by rfl) ⟨4261004, by rfl⟩ : syracuseStep 5681339 = 8522009) B8522009
theorem B1492987 : Blo 698317 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B40389515 : Blo 698317 40389515 := bstep (se 1 (by rfl) ⟨30292136, by rfl⟩ : syracuseStep 40389515 = 60584273) B60584273
theorem B68932577 : Blo 698317 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B5036903 : Blo 698317 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B40984535 : Blo 698317 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B1499257 : Blo 698317 1499257 := bstep (se 2 (by rfl) ⟨562221, by rfl⟩ : syracuseStep 1499257 = 1124443) B1124443
theorem B3039743 : Blo 698317 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B64613447 : Blo 698317 64613447 := bstep (se 1 (by rfl) ⟨48460085, by rfl⟩ : syracuseStep 64613447 = 96920171) B96920171
theorem B5305175 : Blo 698317 5305175 := bstep (se 1 (by rfl) ⟨3978881, by rfl⟩ : syracuseStep 5305175 = 7957763) B7957763
theorem B5994431 : Blo 698317 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B5307119 : Blo 698317 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B8977499 : Blo 698317 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B87522443 : Blo 698317 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B1999009 : Blo 698317 1999009 := bstep (se 2 (by rfl) ⟨749628, by rfl⟩ : syracuseStep 1999009 = 1499257) B1499257
theorem B787135 : Blo 698317 787135 := bstep (se 1 (by rfl) ⟨590351, by rfl⟩ : syracuseStep 787135 = 1180703) B1180703
theorem B1050239 : Blo 698317 1050239 := bstep (se 1 (by rfl) ⟨787679, by rfl⟩ : syracuseStep 1050239 = 1575359) B1575359
theorem B1050491 : Blo 698317 1050491 := bstep (se 1 (by rfl) ⟨787868, by rfl⟩ : syracuseStep 1050491 = 1575737) B1575737
theorem B1050791 : Blo 698317 1050791 := bstep (se 1 (by rfl) ⟨788093, by rfl⟩ : syracuseStep 1050791 = 1576187) B1576187
theorem B1774619 : Blo 698317 1774619 := bstep (se 1 (by rfl) ⟨1330964, by rfl⟩ : syracuseStep 1774619 = 2661929) B2661929
theorem B1578761 : Blo 698317 1578761 := bstep (se 2 (by rfl) ⟨592035, by rfl⟩ : syracuseStep 1578761 = 1184071) B1184071
theorem B1775783 : Blo 698317 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B1776431 : Blo 698317 1776431 := bstep (se 1 (by rfl) ⟨1332323, by rfl⟩ : syracuseStep 1776431 = 2664647) B2664647
theorem B1777403 : Blo 698317 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B699903 : Blo 698317 699903 := bstep (se 1 (by rfl) ⟨524927, by rfl⟩ : syracuseStep 699903 = 1049855) B1049855
theorem B701255 : Blo 698317 701255 := bstep (se 1 (by rfl) ⟨525941, by rfl⟩ : syracuseStep 701255 = 1051883) B1051883
theorem B3554441 : Blo 698317 3554441 := bstep (se 2 (by rfl) ⟨1332915, by rfl⟩ : syracuseStep 3554441 = 2665831) B2665831
theorem B3357935 : Blo 698317 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B2997967 : Blo 698317 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B43075631 : Blo 698317 43075631 := bstep (se 1 (by rfl) ⟨32306723, by rfl⟩ : syracuseStep 43075631 = 64613447) B64613447
theorem B3787559 : Blo 698317 3787559 := bstep (se 1 (by rfl) ⟨2840669, by rfl⟩ : syracuseStep 3787559 = 5681339) B5681339
theorem B5984999 : Blo 698317 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B58348295 : Blo 698317 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B1332703 : Blo 698317 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B6903863 : Blo 698317 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B3366143 : Blo 698317 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B26926343 : Blo 698317 26926343 := bstep (se 1 (by rfl) ⟨20194757, by rfl⟩ : syracuseStep 26926343 = 40389515) B40389515
theorem B183820205 : Blo 698317 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B1990649 : Blo 698317 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B27323023 : Blo 698317 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B2026495 : Blo 698317 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B3536783 : Blo 698317 3536783 := bstep (se 1 (by rfl) ⟨2652587, by rfl⟩ : syracuseStep 3536783 = 5305175) B5305175
theorem B3996287 : Blo 698317 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B3538079 : Blo 698317 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B1049513 : Blo 698317 1049513 := bstep (se 2 (by rfl) ⟨393567, by rfl⟩ : syracuseStep 1049513 = 787135) B787135
theorem B2525039 : Blo 698317 2525039 := bstep (se 1 (by rfl) ⟨1893779, by rfl⟩ : syracuseStep 2525039 = 3787559) B3787559
theorem B38898863 : Blo 698317 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B1183079 : Blo 698317 1183079 := bstep (se 1 (by rfl) ⟨887309, by rfl⟩ : syracuseStep 1183079 = 1774619) B1774619
theorem B1052507 : Blo 698317 1052507 := bstep (se 1 (by rfl) ⟨789380, by rfl⟩ : syracuseStep 1052507 = 1578761) B1578761
theorem B1183855 : Blo 698317 1183855 := bstep (se 1 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 1183855 = 1775783) B1775783
theorem B1184287 : Blo 698317 1184287 := bstep (se 1 (by rfl) ⟨888215, by rfl⟩ : syracuseStep 1184287 = 1776431) B1776431
theorem B1184935 : Blo 698317 1184935 := bstep (se 1 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 1184935 = 1777403) B1777403
theorem B1776937 : Blo 698317 1776937 := bstep (se 2 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 1776937 = 1332703) B1332703
theorem B2664191 : Blo 698317 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B2369627 : Blo 698317 2369627 := bstep (se 1 (by rfl) ⟨1777220, by rfl⟩ : syracuseStep 2369627 = 3554441) B3554441
theorem B2238623 : Blo 698317 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B2665345 : Blo 698317 2665345 := bstep (se 2 (by rfl) ⟨999504, by rfl⟩ : syracuseStep 2665345 = 1999009) B1999009
theorem B700159 : Blo 698317 700159 := bstep (se 1 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 700159 = 1050239) B1050239
theorem B700327 : Blo 698317 700327 := bstep (se 1 (by rfl) ⟨525245, by rfl⟩ : syracuseStep 700327 = 1050491) B1050491
theorem B28717087 : Blo 698317 28717087 := bstep (se 1 (by rfl) ⟨21537815, by rfl⟩ : syracuseStep 28717087 = 43075631) B43075631
theorem B700527 : Blo 698317 700527 := bstep (se 1 (by rfl) ⟨525395, by rfl⟩ : syracuseStep 700527 = 1050791) B1050791
theorem B2701993 : Blo 698317 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B4602575 : Blo 698317 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B2244095 : Blo 698317 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B1327099 : Blo 698317 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B3989999 : Blo 698317 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B36430697 : Blo 698317 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B17950895 : Blo 698317 17950895 := bstep (se 1 (by rfl) ⟨13463171, by rfl⟩ : syracuseStep 17950895 = 26926343) B26926343
theorem B122546803 : Blo 698317 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B2357855 : Blo 698317 2357855 := bstep (se 1 (by rfl) ⟨1768391, by rfl⟩ : syracuseStep 2357855 = 3536783) B3536783
theorem B2358719 : Blo 698317 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B3997289 : Blo 698317 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B788719 : Blo 698317 788719 := bstep (se 1 (by rfl) ⟨591539, by rfl⟩ : syracuseStep 788719 = 1183079) B1183079
theorem B1578473 : Blo 698317 1578473 := bstep (se 2 (by rfl) ⟨591927, by rfl⟩ : syracuseStep 1578473 = 1183855) B1183855
theorem B2659999 : Blo 698317 2659999 := bstep (se 1 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 2659999 = 3989999) B3989999
theorem B24287131 : Blo 698317 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B1579049 : Blo 698317 1579049 := bstep (se 2 (by rfl) ⟨592143, by rfl⟩ : syracuseStep 1579049 = 1184287) B1184287
theorem B1776127 : Blo 698317 1776127 := bstep (se 1 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 1776127 = 2664191) B2664191
theorem B1579751 : Blo 698317 1579751 := bstep (se 1 (by rfl) ⟨1184813, by rfl⟩ : syracuseStep 1579751 = 2369627) B2369627
theorem B11967263 : Blo 698317 11967263 := bstep (se 1 (by rfl) ⟨8975447, by rfl⟩ : syracuseStep 11967263 = 17950895) B17950895
theorem B1579913 : Blo 698317 1579913 := bstep (se 2 (by rfl) ⟨592467, by rfl⟩ : syracuseStep 1579913 = 1184935) B1184935
theorem B2369249 : Blo 698317 2369249 := bstep (se 2 (by rfl) ⟨888468, by rfl⟩ : syracuseStep 2369249 = 1776937) B1776937
theorem B2664859 : Blo 698317 2664859 := bstep (se 1 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 2664859 = 3997289) B3997289
theorem B699675 : Blo 698317 699675 := bstep (se 1 (by rfl) ⟨524756, by rfl⟩ : syracuseStep 699675 = 1049513) B1049513
theorem B1683359 : Blo 698317 1683359 := bstep (se 1 (by rfl) ⟨1262519, by rfl⟩ : syracuseStep 1683359 = 2525039) B2525039
theorem B25932575 : Blo 698317 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B701671 : Blo 698317 701671 := bstep (se 1 (by rfl) ⟨526253, by rfl⟩ : syracuseStep 701671 = 1052507) B1052507
theorem B163395737 : Blo 698317 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B3553793 : Blo 698317 3553793 := bstep (se 2 (by rfl) ⟨1332672, by rfl⟩ : syracuseStep 3553793 = 2665345) B2665345
theorem B38289449 : Blo 698317 38289449 := bstep (se 2 (by rfl) ⟨14358543, by rfl⟩ : syracuseStep 38289449 = 28717087) B28717087
theorem B1492415 : Blo 698317 1492415 := bstep (se 1 (by rfl) ⟨1119311, by rfl⟩ : syracuseStep 1492415 = 2238623) B2238623
theorem B3068383 : Blo 698317 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B1496063 : Blo 698317 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B3602657 : Blo 698317 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B1571903 : Blo 698317 1571903 := bstep (se 1 (by rfl) ⟨1178927, by rfl⟩ : syracuseStep 1571903 = 2357855) B2357855
theorem B1572479 : Blo 698317 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B1769465 : Blo 698317 1769465 := bstep (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) B1327099
theorem B25526299 : Blo 698317 25526299 := bstep (se 1 (by rfl) ⟨19144724, by rfl⟩ : syracuseStep 25526299 = 38289449) B38289449
theorem B1051625 : Blo 698317 1051625 := bstep (se 2 (by rfl) ⟨394359, by rfl⟩ : syracuseStep 1051625 = 788719) B788719
theorem B1052315 : Blo 698317 1052315 := bstep (se 1 (by rfl) ⟨789236, by rfl⟩ : syracuseStep 1052315 = 1578473) B1578473
theorem B1052699 : Blo 698317 1052699 := bstep (se 1 (by rfl) ⟨789524, by rfl⟩ : syracuseStep 1052699 = 1579049) B1579049
theorem B1053167 : Blo 698317 1053167 := bstep (se 1 (by rfl) ⟨789875, by rfl⟩ : syracuseStep 1053167 = 1579751) B1579751
theorem B1053275 : Blo 698317 1053275 := bstep (se 1 (by rfl) ⟨789956, by rfl⟩ : syracuseStep 1053275 = 1579913) B1579913
theorem B1579499 : Blo 698317 1579499 := bstep (se 1 (by rfl) ⟨1184624, by rfl⟩ : syracuseStep 1579499 = 2369249) B2369249
theorem B3546665 : Blo 698317 3546665 := bstep (se 2 (by rfl) ⟨1329999, by rfl⟩ : syracuseStep 3546665 = 2659999) B2659999
theorem B32382841 : Blo 698317 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B1122239 : Blo 698317 1122239 := bstep (se 1 (by rfl) ⟨841679, by rfl⟩ : syracuseStep 1122239 = 1683359) B1683359
theorem B2368169 : Blo 698317 2368169 := bstep (se 2 (by rfl) ⟨888063, by rfl⟩ : syracuseStep 2368169 = 1776127) B1776127
theorem B108930491 : Blo 698317 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B2401771 : Blo 698317 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B2369195 : Blo 698317 2369195 := bstep (se 1 (by rfl) ⟨1776896, by rfl⟩ : syracuseStep 2369195 = 3553793) B3553793
theorem B994943 : Blo 698317 994943 := bstep (se 1 (by rfl) ⟨746207, by rfl⟩ : syracuseStep 994943 = 1492415) B1492415
theorem B69153533 : Blo 698317 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B3553145 : Blo 698317 3553145 := bstep (se 2 (by rfl) ⟨1332429, by rfl⟩ : syracuseStep 3553145 = 2664859) B2664859
theorem B997375 : Blo 698317 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B7978175 : Blo 698317 7978175 := bstep (se 1 (by rfl) ⟨5983631, by rfl⟩ : syracuseStep 7978175 = 11967263) B11967263
theorem B4091177 : Blo 698317 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B1047935 : Blo 698317 1047935 := bstep (se 1 (by rfl) ⟨785951, by rfl⟩ : syracuseStep 1047935 = 1571903) B1571903
theorem B1048319 : Blo 698317 1048319 := bstep (se 1 (by rfl) ⟨786239, by rfl⟩ : syracuseStep 1048319 = 1572479) B1572479
theorem B1179643 : Blo 698317 1179643 := bstep (se 1 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 1179643 = 1769465) B1769465
theorem B1052999 : Blo 698317 1052999 := bstep (se 1 (by rfl) ⟨789749, by rfl⟩ : syracuseStep 1052999 = 1579499) B1579499
theorem B2364443 : Blo 698317 2364443 := bstep (se 1 (by rfl) ⟨1773332, by rfl⟩ : syracuseStep 2364443 = 3546665) B3546665
theorem B1578779 : Blo 698317 1578779 := bstep (se 1 (by rfl) ⟨1184084, by rfl⟩ : syracuseStep 1578779 = 2368169) B2368169
theorem B72620327 : Blo 698317 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B1579463 : Blo 698317 1579463 := bstep (se 1 (by rfl) ⟨1184597, by rfl⟩ : syracuseStep 1579463 = 2369195) B2369195
theorem B2727451 : Blo 698317 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B2368763 : Blo 698317 2368763 := bstep (se 1 (by rfl) ⟨1776572, by rfl⟩ : syracuseStep 2368763 = 3553145) B3553145
theorem B5318783 : Blo 698317 5318783 := bstep (se 1 (by rfl) ⟨3989087, by rfl⟩ : syracuseStep 5318783 = 7978175) B7978175
theorem B698623 : Blo 698317 698623 := bstep (se 1 (by rfl) ⟨523967, by rfl⟩ : syracuseStep 698623 = 1047935) B1047935
theorem B698879 : Blo 698317 698879 := bstep (se 1 (by rfl) ⟨524159, by rfl⟩ : syracuseStep 698879 = 1048319) B1048319
theorem B701083 : Blo 698317 701083 := bstep (se 1 (by rfl) ⟨525812, by rfl⟩ : syracuseStep 701083 = 1051625) B1051625
theorem B701543 : Blo 698317 701543 := bstep (se 1 (by rfl) ⟨526157, by rfl⟩ : syracuseStep 701543 = 1052315) B1052315
theorem B701799 : Blo 698317 701799 := bstep (se 1 (by rfl) ⟨526349, by rfl⟩ : syracuseStep 701799 = 1052699) B1052699
theorem B702111 : Blo 698317 702111 := bstep (se 1 (by rfl) ⟨526583, by rfl⟩ : syracuseStep 702111 = 1053167) B1053167
theorem B702183 : Blo 698317 702183 := bstep (se 1 (by rfl) ⟨526637, by rfl⟩ : syracuseStep 702183 = 1053275) B1053275
theorem B1572857 : Blo 698317 1572857 := bstep (se 2 (by rfl) ⟨589821, by rfl⟩ : syracuseStep 1572857 = 1179643) B1179643
theorem B1329833 : Blo 698317 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B43177121 : Blo 698317 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B34035065 : Blo 698317 34035065 := bstep (se 2 (by rfl) ⟨12763149, by rfl⟩ : syracuseStep 34035065 = 25526299) B25526299
theorem B3202361 : Blo 698317 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B748159 : Blo 698317 748159 := bstep (se 1 (by rfl) ⟨561119, by rfl⟩ : syracuseStep 748159 = 1122239) B1122239
theorem B46102355 : Blo 698317 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B2653181 : Blo 698317 2653181 := bstep (se 3 (by rfl) ⟨497471, by rfl⟩ : syracuseStep 2653181 = 994943) B994943
theorem B886555 : Blo 698317 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B1576295 : Blo 698317 1576295 := bstep (se 1 (by rfl) ⟨1182221, by rfl⟩ : syracuseStep 1576295 = 2364443) B2364443
theorem B1052519 : Blo 698317 1052519 := bstep (se 1 (by rfl) ⟨789389, by rfl⟩ : syracuseStep 1052519 = 1578779) B1578779
theorem B1052975 : Blo 698317 1052975 := bstep (se 1 (by rfl) ⟨789731, by rfl⟩ : syracuseStep 1052975 = 1579463) B1579463
theorem B2134907 : Blo 698317 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B1579175 : Blo 698317 1579175 := bstep (se 1 (by rfl) ⟨1184381, by rfl⟩ : syracuseStep 1579175 = 2368763) B2368763
theorem B3545855 : Blo 698317 3545855 := bstep (se 1 (by rfl) ⟨2659391, by rfl⟩ : syracuseStep 3545855 = 5318783) B5318783
theorem B701999 : Blo 698317 701999 := bstep (se 1 (by rfl) ⟨526499, by rfl⟩ : syracuseStep 701999 = 1052999) B1052999
theorem B28784747 : Blo 698317 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B22690043 : Blo 698317 22690043 := bstep (se 1 (by rfl) ⟨17017532, by rfl⟩ : syracuseStep 22690043 = 34035065) B34035065
theorem B48413551 : Blo 698317 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B3990181 : Blo 698317 3990181 := bstep (se 4 (by rfl) ⟨374079, by rfl⟩ : syracuseStep 3990181 = 748159) B748159
theorem B14546405 : Blo 698317 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B30734903 : Blo 698317 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B1768787 : Blo 698317 1768787 := bstep (se 1 (by rfl) ⟨1326590, by rfl⟩ : syracuseStep 1768787 = 2653181) B2653181
theorem B1048571 : Blo 698317 1048571 := bstep (se 1 (by rfl) ⟨786428, by rfl⟩ : syracuseStep 1048571 = 1572857) B1572857
theorem B1050863 : Blo 698317 1050863 := bstep (se 1 (by rfl) ⟨788147, by rfl⟩ : syracuseStep 1050863 = 1576295) B1576295
theorem B1182073 : Blo 698317 1182073 := bstep (se 2 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 1182073 = 886555) B886555
theorem B1052783 : Blo 698317 1052783 := bstep (se 1 (by rfl) ⟨789587, by rfl⟩ : syracuseStep 1052783 = 1579175) B1579175
theorem B2363903 : Blo 698317 2363903 := bstep (se 1 (by rfl) ⟨1772927, by rfl⟩ : syracuseStep 2363903 = 3545855) B3545855
theorem B20489935 : Blo 698317 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B699047 : Blo 698317 699047 := bstep (se 1 (by rfl) ⟨524285, by rfl⟩ : syracuseStep 699047 = 1048571) B1048571
theorem B5320241 : Blo 698317 5320241 := bstep (se 2 (by rfl) ⟨1995090, by rfl⟩ : syracuseStep 5320241 = 3990181) B3990181
theorem B701679 : Blo 698317 701679 := bstep (se 1 (by rfl) ⟨526259, by rfl⟩ : syracuseStep 701679 = 1052519) B1052519
theorem B701983 : Blo 698317 701983 := bstep (se 1 (by rfl) ⟨526487, by rfl⟩ : syracuseStep 701983 = 1052975) B1052975
theorem B1423271 : Blo 698317 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B76759325 : Blo 698317 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B15126695 : Blo 698317 15126695 := bstep (se 1 (by rfl) ⟨11345021, by rfl⟩ : syracuseStep 15126695 = 22690043) B22690043
theorem B9697603 : Blo 698317 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B64551401 : Blo 698317 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B1179191 : Blo 698317 1179191 := bstep (se 1 (by rfl) ⟨884393, by rfl⟩ : syracuseStep 1179191 = 1768787) B1768787
theorem B1575935 : Blo 698317 1575935 := bstep (se 1 (by rfl) ⟨1181951, by rfl⟩ : syracuseStep 1575935 = 2363903) B2363903
theorem B1576097 : Blo 698317 1576097 := bstep (se 2 (by rfl) ⟨591036, by rfl⟩ : syracuseStep 1576097 = 1182073) B1182073
theorem B3546827 : Blo 698317 3546827 := bstep (se 1 (by rfl) ⟨2660120, by rfl⟩ : syracuseStep 3546827 = 5320241) B5320241
theorem B43034267 : Blo 698317 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B700575 : Blo 698317 700575 := bstep (se 1 (by rfl) ⟨525431, by rfl⟩ : syracuseStep 700575 = 1050863) B1050863
theorem B701855 : Blo 698317 701855 := bstep (se 1 (by rfl) ⟨526391, by rfl⟩ : syracuseStep 701855 = 1052783) B1052783
theorem B12930137 : Blo 698317 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B51172883 : Blo 698317 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B27319913 : Blo 698317 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B10084463 : Blo 698317 10084463 := bstep (se 1 (by rfl) ⟨7563347, by rfl⟩ : syracuseStep 10084463 = 15126695) B15126695
theorem B948847 : Blo 698317 948847 := bstep (se 1 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 948847 = 1423271) B1423271
theorem B786127 : Blo 698317 786127 := bstep (se 1 (by rfl) ⟨589595, by rfl⟩ : syracuseStep 786127 = 1179191) B1179191
theorem B1050623 : Blo 698317 1050623 := bstep (se 1 (by rfl) ⟨787967, by rfl⟩ : syracuseStep 1050623 = 1575935) B1575935
theorem B8620091 : Blo 698317 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B1050731 : Blo 698317 1050731 := bstep (se 1 (by rfl) ⟨788048, by rfl⟩ : syracuseStep 1050731 = 1576097) B1576097
theorem B34115255 : Blo 698317 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B2364551 : Blo 698317 2364551 := bstep (se 1 (by rfl) ⟨1773413, by rfl⟩ : syracuseStep 2364551 = 3546827) B3546827
theorem B6722975 : Blo 698317 6722975 := bstep (se 1 (by rfl) ⟨5042231, by rfl⟩ : syracuseStep 6722975 = 10084463) B10084463
theorem B28689511 : Blo 698317 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B1265129 : Blo 698317 1265129 := bstep (se 2 (by rfl) ⟨474423, by rfl⟩ : syracuseStep 1265129 = 948847) B948847
theorem B18213275 : Blo 698317 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B1048169 : Blo 698317 1048169 := bstep (se 2 (by rfl) ⟨393063, by rfl⟩ : syracuseStep 1048169 = 786127) B786127
theorem B22743503 : Blo 698317 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B1576367 : Blo 698317 1576367 := bstep (se 1 (by rfl) ⟨1182275, by rfl⟩ : syracuseStep 1576367 = 2364551) B2364551
theorem B698779 : Blo 698317 698779 := bstep (se 1 (by rfl) ⟨524084, by rfl⟩ : syracuseStep 698779 = 1048169) B1048169
theorem B700415 : Blo 698317 700415 := bstep (se 1 (by rfl) ⟨525311, by rfl⟩ : syracuseStep 700415 = 1050623) B1050623
theorem B5746727 : Blo 698317 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B700487 : Blo 698317 700487 := bstep (se 1 (by rfl) ⟨525365, by rfl⟩ : syracuseStep 700487 = 1050731) B1050731
theorem B38252681 : Blo 698317 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B12142183 : Blo 698317 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B843419 : Blo 698317 843419 := bstep (se 1 (by rfl) ⟨632564, by rfl⟩ : syracuseStep 843419 = 1265129) B1265129
theorem B4481983 : Blo 698317 4481983 := bstep (se 1 (by rfl) ⟨3361487, by rfl⟩ : syracuseStep 4481983 = 6722975) B6722975
theorem B16189577 : Blo 698317 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B1050911 : Blo 698317 1050911 := bstep (se 1 (by rfl) ⟨788183, by rfl⟩ : syracuseStep 1050911 = 1576367) B1576367
theorem B25501787 : Blo 698317 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B5975977 : Blo 698317 5975977 := bstep (se 2 (by rfl) ⟨2240991, by rfl⟩ : syracuseStep 5975977 = 4481983) B4481983
theorem B2249117 : Blo 698317 2249117 := bstep (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) B843419
theorem B15162335 : Blo 698317 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B3831151 : Blo 698317 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B7967969 : Blo 698317 7967969 := bstep (se 2 (by rfl) ⟨2987988, by rfl⟩ : syracuseStep 7967969 = 5975977) B5975977
theorem B10793051 : Blo 698317 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B700607 : Blo 698317 700607 := bstep (se 1 (by rfl) ⟨525455, by rfl⟩ : syracuseStep 700607 = 1050911) B1050911
theorem B10108223 : Blo 698317 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B1499411 : Blo 698317 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B17001191 : Blo 698317 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B5108201 : Blo 698317 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B3998429 : Blo 698317 3998429 := bstep (se 3 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 3998429 = 1499411) B1499411
theorem B5311979 : Blo 698317 5311979 := bstep (se 1 (by rfl) ⟨3983984, by rfl⟩ : syracuseStep 5311979 = 7967969) B7967969
theorem B7195367 : Blo 698317 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B6738815 : Blo 698317 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B11334127 : Blo 698317 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B3405467 : Blo 698317 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B3541319 : Blo 698317 3541319 := bstep (se 1 (by rfl) ⟨2655989, by rfl⟩ : syracuseStep 3541319 = 5311979) B5311979
theorem B4492543 : Blo 698317 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B15112169 : Blo 698317 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B2270311 : Blo 698317 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B2665619 : Blo 698317 2665619 := bstep (se 1 (by rfl) ⟨1999214, by rfl⟩ : syracuseStep 2665619 = 3998429) B3998429
theorem B4796911 : Blo 698317 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B2360879 : Blo 698317 2360879 := bstep (se 1 (by rfl) ⟨1770659, by rfl⟩ : syracuseStep 2360879 = 3541319) B3541319
theorem B1777079 : Blo 698317 1777079 := bstep (se 1 (by rfl) ⟨1332809, by rfl⟩ : syracuseStep 1777079 = 2665619) B2665619
theorem B10074779 : Blo 698317 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B12108325 : Blo 698317 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B25583525 : Blo 698317 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B5990057 : Blo 698317 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B1573919 : Blo 698317 1573919 := bstep (se 1 (by rfl) ⟨1180439, by rfl⟩ : syracuseStep 1573919 = 2360879) B2360879
theorem B1184719 : Blo 698317 1184719 := bstep (se 1 (by rfl) ⟨888539, by rfl⟩ : syracuseStep 1184719 = 1777079) B1777079
theorem B17055683 : Blo 698317 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B16144433 : Blo 698317 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B3993371 : Blo 698317 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B6716519 : Blo 698317 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B1049279 : Blo 698317 1049279 := bstep (se 1 (by rfl) ⟨786959, by rfl⟩ : syracuseStep 1049279 = 1573919) B1573919
theorem B1579625 : Blo 698317 1579625 := bstep (se 2 (by rfl) ⟨592359, by rfl⟩ : syracuseStep 1579625 = 1184719) B1184719
theorem B2662247 : Blo 698317 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B10762955 : Blo 698317 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B4477679 : Blo 698317 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B11370455 : Blo 698317 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B2985119 : Blo 698317 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B1053083 : Blo 698317 1053083 := bstep (se 1 (by rfl) ⟨789812, by rfl⟩ : syracuseStep 1053083 = 1579625) B1579625
theorem B1774831 : Blo 698317 1774831 := bstep (se 1 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 1774831 = 2662247) B2662247
theorem B7580303 : Blo 698317 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B699519 : Blo 698317 699519 := bstep (se 1 (by rfl) ⟨524639, by rfl⟩ : syracuseStep 699519 = 1049279) B1049279
theorem B7175303 : Blo 698317 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B2366441 : Blo 698317 2366441 := bstep (se 2 (by rfl) ⟨887415, by rfl⟩ : syracuseStep 2366441 = 1774831) B1774831
theorem B5053535 : Blo 698317 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B702055 : Blo 698317 702055 := bstep (se 1 (by rfl) ⟨526541, by rfl⟩ : syracuseStep 702055 = 1053083) B1053083
theorem B1990079 : Blo 698317 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B4783535 : Blo 698317 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B1577627 : Blo 698317 1577627 := bstep (se 1 (by rfl) ⟨1183220, by rfl⟩ : syracuseStep 1577627 = 2366441) B2366441
theorem B3189023 : Blo 698317 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B1326719 : Blo 698317 1326719 := bstep (se 1 (by rfl) ⟨995039, by rfl⟩ : syracuseStep 1326719 = 1990079) B1990079
theorem B3369023 : Blo 698317 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B1051751 : Blo 698317 1051751 := bstep (se 1 (by rfl) ⟨788813, by rfl⟩ : syracuseStep 1051751 = 1577627) B1577627
theorem B2246015 : Blo 698317 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B2126015 : Blo 698317 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B3537917 : Blo 698317 3537917 := bstep (se 3 (by rfl) ⟨663359, by rfl⟩ : syracuseStep 3537917 = 1326719) B1326719
theorem B1417343 : Blo 698317 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B701167 : Blo 698317 701167 := bstep (se 1 (by rfl) ⟨525875, by rfl⟩ : syracuseStep 701167 = 1051751) B1051751
theorem B5989373 : Blo 698317 5989373 := bstep (se 3 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 5989373 = 2246015) B2246015
theorem B2358611 : Blo 698317 2358611 := bstep (se 1 (by rfl) ⟨1768958, by rfl⟩ : syracuseStep 2358611 = 3537917) B3537917
theorem B3779581 : Blo 698317 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B3992915 : Blo 698317 3992915 := bstep (se 1 (by rfl) ⟨2994686, by rfl⟩ : syracuseStep 3992915 = 5989373) B5989373
theorem B1572407 : Blo 698317 1572407 := bstep (se 1 (by rfl) ⟨1179305, by rfl⟩ : syracuseStep 1572407 = 2358611) B2358611
theorem B2661943 : Blo 698317 2661943 := bstep (se 1 (by rfl) ⟨1996457, by rfl⟩ : syracuseStep 2661943 = 3992915) B3992915
theorem B5039441 : Blo 698317 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B1048271 : Blo 698317 1048271 := bstep (se 1 (by rfl) ⟨786203, by rfl⟩ : syracuseStep 1048271 = 1572407) B1572407
theorem B3549257 : Blo 698317 3549257 := bstep (se 2 (by rfl) ⟨1330971, by rfl⟩ : syracuseStep 3549257 = 2661943) B2661943
theorem B698847 : Blo 698317 698847 := bstep (se 1 (by rfl) ⟨524135, by rfl⟩ : syracuseStep 698847 = 1048271) B1048271
theorem B3359627 : Blo 698317 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B2366171 : Blo 698317 2366171 := bstep (se 1 (by rfl) ⟨1774628, by rfl⟩ : syracuseStep 2366171 = 3549257) B3549257
theorem B2239751 : Blo 698317 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B1577447 : Blo 698317 1577447 := bstep (se 1 (by rfl) ⟨1183085, by rfl⟩ : syracuseStep 1577447 = 2366171) B2366171
theorem B1493167 : Blo 698317 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B1051631 : Blo 698317 1051631 := bstep (se 1 (by rfl) ⟨788723, by rfl⟩ : syracuseStep 1051631 = 1577447) B1577447
theorem B1990889 : Blo 698317 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B701087 : Blo 698317 701087 := bstep (se 1 (by rfl) ⟨525815, by rfl⟩ : syracuseStep 701087 = 1051631) B1051631
theorem B1327259 : Blo 698317 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889
theorem B884839 : Blo 698317 884839 := bstep (se 1 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 884839 = 1327259) B1327259
theorem B1179785 : Blo 698317 1179785 := bstep (se 2 (by rfl) ⟨442419, by rfl⟩ : syracuseStep 1179785 = 884839) B884839
theorem B786523 : Blo 698317 786523 := bstep (se 1 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 786523 = 1179785) B1179785
theorem B1048697 : Blo 698317 1048697 := bstep (se 2 (by rfl) ⟨393261, by rfl⟩ : syracuseStep 1048697 = 786523) B786523
theorem B699131 : Blo 698317 699131 := bstep (se 1 (by rfl) ⟨524348, by rfl⟩ : syracuseStep 699131 = 1048697) B1048697

theorem C0 (j : ℕ) (h1 : 174579 ≤ j) (h2 : j ≤ 175278) : Blo 698317 (4 * j + 3) := by
  interval_cases j
  · exact B698319
  · exact B698323
  · exact B698327
  · exact B698331
  · exact B698335
  · exact B698339
  · exact B698343
  · exact B698347
  · exact B698351
  · exact B698355
  · exact B698359
  · exact B698363
  · exact B698367
  · exact B698371
  · exact B698375
  · exact B698379
  · exact B698383
  · exact B698387
  · exact B698391
  · exact B698395
  · exact B698399
  · exact B698403
  · exact B698407
  · exact B698411
  · exact B698415
  · exact B698419
  · exact B698423
  · exact B698427
  · exact B698431
  · exact B698435
  · exact B698439
  · exact B698443
  · exact B698447
  · exact B698451
  · exact B698455
  · exact B698459
  · exact B698463
  · exact B698467
  · exact B698471
  · exact B698475
  · exact B698479
  · exact B698483
  · exact B698487
  · exact B698491
  · exact B698495
  · exact B698499
  · exact B698503
  · exact B698507
  · exact B698511
  · exact B698515
  · exact B698519
  · exact B698523
  · exact B698527
  · exact B698531
  · exact B698535
  · exact B698539
  · exact B698543
  · exact B698547
  · exact B698551
  · exact B698555
  · exact B698559
  · exact B698563
  · exact B698567
  · exact B698571
  · exact B698575
  · exact B698579
  · exact B698583
  · exact B698587
  · exact B698591
  · exact B698595
  · exact B698599
  · exact B698603
  · exact B698607
  · exact B698611
  · exact B698615
  · exact B698619
  · exact B698623
  · exact B698627
  · exact B698631
  · exact B698635
  · exact B698639
  · exact B698643
  · exact B698647
  · exact B698651
  · exact B698655
  · exact B698659
  · exact B698663
  · exact B698667
  · exact B698671
  · exact B698675
  · exact B698679
  · exact B698683
  · exact B698687
  · exact B698691
  · exact B698695
  · exact B698699
  · exact B698703
  · exact B698707
  · exact B698711
  · exact B698715
  · exact B698719
  · exact B698723
  · exact B698727
  · exact B698731
  · exact B698735
  · exact B698739
  · exact B698743
  · exact B698747
  · exact B698751
  · exact B698755
  · exact B698759
  · exact B698763
  · exact B698767
  · exact B698771
  · exact B698775
  · exact B698779
  · exact B698783
  · exact B698787
  · exact B698791
  · exact B698795
  · exact B698799
  · exact B698803
  · exact B698807
  · exact B698811
  · exact B698815
  · exact B698819
  · exact B698823
  · exact B698827
  · exact B698831
  · exact B698835
  · exact B698839
  · exact B698843
  · exact B698847
  · exact B698851
  · exact B698855
  · exact B698859
  · exact B698863
  · exact B698867
  · exact B698871
  · exact B698875
  · exact B698879
  · exact B698883
  · exact B698887
  · exact B698891
  · exact B698895
  · exact B698899
  · exact B698903
  · exact B698907
  · exact B698911
  · exact B698915
  · exact B698919
  · exact B698923
  · exact B698927
  · exact B698931
  · exact B698935
  · exact B698939
  · exact B698943
  · exact B698947
  · exact B698951
  · exact B698955
  · exact B698959
  · exact B698963
  · exact B698967
  · exact B698971
  · exact B698975
  · exact B698979
  · exact B698983
  · exact B698987
  · exact B698991
  · exact B698995
  · exact B698999
  · exact B699003
  · exact B699007
  · exact B699011
  · exact B699015
  · exact B699019
  · exact B699023
  · exact B699027
  · exact B699031
  · exact B699035
  · exact B699039
  · exact B699043
  · exact B699047
  · exact B699051
  · exact B699055
  · exact B699059
  · exact B699063
  · exact B699067
  · exact B699071
  · exact B699075
  · exact B699079
  · exact B699083
  · exact B699087
  · exact B699091
  · exact B699095
  · exact B699099
  · exact B699103
  · exact B699107
  · exact B699111
  · exact B699115
  · exact B699119
  · exact B699123
  · exact B699127
  · exact B699131
  · exact B699135
  · exact B699139
  · exact B699143
  · exact B699147
  · exact B699151
  · exact B699155
  · exact B699159
  · exact B699163
  · exact B699167
  · exact B699171
  · exact B699175
  · exact B699179
  · exact B699183
  · exact B699187
  · exact B699191
  · exact B699195
  · exact B699199
  · exact B699203
  · exact B699207
  · exact B699211
  · exact B699215
  · exact B699219
  · exact B699223
  · exact B699227
  · exact B699231
  · exact B699235
  · exact B699239
  · exact B699243
  · exact B699247
  · exact B699251
  · exact B699255
  · exact B699259
  · exact B699263
  · exact B699267
  · exact B699271
  · exact B699275
  · exact B699279
  · exact B699283
  · exact B699287
  · exact B699291
  · exact B699295
  · exact B699299
  · exact B699303
  · exact B699307
  · exact B699311
  · exact B699315
  · exact B699319
  · exact B699323
  · exact B699327
  · exact B699331
  · exact B699335
  · exact B699339
  · exact B699343
  · exact B699347
  · exact B699351
  · exact B699355
  · exact B699359
  · exact B699363
  · exact B699367
  · exact B699371
  · exact B699375
  · exact B699379
  · exact B699383
  · exact B699387
  · exact B699391
  · exact B699395
  · exact B699399
  · exact B699403
  · exact B699407
  · exact B699411
  · exact B699415
  · exact B699419
  · exact B699423
  · exact B699427
  · exact B699431
  · exact B699435
  · exact B699439
  · exact B699443
  · exact B699447
  · exact B699451
  · exact B699455
  · exact B699459
  · exact B699463
  · exact B699467
  · exact B699471
  · exact B699475
  · exact B699479
  · exact B699483
  · exact B699487
  · exact B699491
  · exact B699495
  · exact B699499
  · exact B699503
  · exact B699507
  · exact B699511
  · exact B699515
  · exact B699519
  · exact B699523
  · exact B699527
  · exact B699531
  · exact B699535
  · exact B699539
  · exact B699543
  · exact B699547
  · exact B699551
  · exact B699555
  · exact B699559
  · exact B699563
  · exact B699567
  · exact B699571
  · exact B699575
  · exact B699579
  · exact B699583
  · exact B699587
  · exact B699591
  · exact B699595
  · exact B699599
  · exact B699603
  · exact B699607
  · exact B699611
  · exact B699615
  · exact B699619
  · exact B699623
  · exact B699627
  · exact B699631
  · exact B699635
  · exact B699639
  · exact B699643
  · exact B699647
  · exact B699651
  · exact B699655
  · exact B699659
  · exact B699663
  · exact B699667
  · exact B699671
  · exact B699675
  · exact B699679
  · exact B699683
  · exact B699687
  · exact B699691
  · exact B699695
  · exact B699699
  · exact B699703
  · exact B699707
  · exact B699711
  · exact B699715
  · exact B699719
  · exact B699723
  · exact B699727
  · exact B699731
  · exact B699735
  · exact B699739
  · exact B699743
  · exact B699747
  · exact B699751
  · exact B699755
  · exact B699759
  · exact B699763
  · exact B699767
  · exact B699771
  · exact B699775
  · exact B699779
  · exact B699783
  · exact B699787
  · exact B699791
  · exact B699795
  · exact B699799
  · exact B699803
  · exact B699807
  · exact B699811
  · exact B699815
  · exact B699819
  · exact B699823
  · exact B699827
  · exact B699831
  · exact B699835
  · exact B699839
  · exact B699843
  · exact B699847
  · exact B699851
  · exact B699855
  · exact B699859
  · exact B699863
  · exact B699867
  · exact B699871
  · exact B699875
  · exact B699879
  · exact B699883
  · exact B699887
  · exact B699891
  · exact B699895
  · exact B699899
  · exact B699903
  · exact B699907
  · exact B699911
  · exact B699915
  · exact B699919
  · exact B699923
  · exact B699927
  · exact B699931
  · exact B699935
  · exact B699939
  · exact B699943
  · exact B699947
  · exact B699951
  · exact B699955
  · exact B699959
  · exact B699963
  · exact B699967
  · exact B699971
  · exact B699975
  · exact B699979
  · exact B699983
  · exact B699987
  · exact B699991
  · exact B699995
  · exact B699999
  · exact B700003
  · exact B700007
  · exact B700011
  · exact B700015
  · exact B700019
  · exact B700023
  · exact B700027
  · exact B700031
  · exact B700035
  · exact B700039
  · exact B700043
  · exact B700047
  · exact B700051
  · exact B700055
  · exact B700059
  · exact B700063
  · exact B700067
  · exact B700071
  · exact B700075
  · exact B700079
  · exact B700083
  · exact B700087
  · exact B700091
  · exact B700095
  · exact B700099
  · exact B700103
  · exact B700107
  · exact B700111
  · exact B700115
  · exact B700119
  · exact B700123
  · exact B700127
  · exact B700131
  · exact B700135
  · exact B700139
  · exact B700143
  · exact B700147
  · exact B700151
  · exact B700155
  · exact B700159
  · exact B700163
  · exact B700167
  · exact B700171
  · exact B700175
  · exact B700179
  · exact B700183
  · exact B700187
  · exact B700191
  · exact B700195
  · exact B700199
  · exact B700203
  · exact B700207
  · exact B700211
  · exact B700215
  · exact B700219
  · exact B700223
  · exact B700227
  · exact B700231
  · exact B700235
  · exact B700239
  · exact B700243
  · exact B700247
  · exact B700251
  · exact B700255
  · exact B700259
  · exact B700263
  · exact B700267
  · exact B700271
  · exact B700275
  · exact B700279
  · exact B700283
  · exact B700287
  · exact B700291
  · exact B700295
  · exact B700299
  · exact B700303
  · exact B700307
  · exact B700311
  · exact B700315
  · exact B700319
  · exact B700323
  · exact B700327
  · exact B700331
  · exact B700335
  · exact B700339
  · exact B700343
  · exact B700347
  · exact B700351
  · exact B700355
  · exact B700359
  · exact B700363
  · exact B700367
  · exact B700371
  · exact B700375
  · exact B700379
  · exact B700383
  · exact B700387
  · exact B700391
  · exact B700395
  · exact B700399
  · exact B700403
  · exact B700407
  · exact B700411
  · exact B700415
  · exact B700419
  · exact B700423
  · exact B700427
  · exact B700431
  · exact B700435
  · exact B700439
  · exact B700443
  · exact B700447
  · exact B700451
  · exact B700455
  · exact B700459
  · exact B700463
  · exact B700467
  · exact B700471
  · exact B700475
  · exact B700479
  · exact B700483
  · exact B700487
  · exact B700491
  · exact B700495
  · exact B700499
  · exact B700503
  · exact B700507
  · exact B700511
  · exact B700515
  · exact B700519
  · exact B700523
  · exact B700527
  · exact B700531
  · exact B700535
  · exact B700539
  · exact B700543
  · exact B700547
  · exact B700551
  · exact B700555
  · exact B700559
  · exact B700563
  · exact B700567
  · exact B700571
  · exact B700575
  · exact B700579
  · exact B700583
  · exact B700587
  · exact B700591
  · exact B700595
  · exact B700599
  · exact B700603
  · exact B700607
  · exact B700611
  · exact B700615
  · exact B700619
  · exact B700623
  · exact B700627
  · exact B700631
  · exact B700635
  · exact B700639
  · exact B700643
  · exact B700647
  · exact B700651
  · exact B700655
  · exact B700659
  · exact B700663
  · exact B700667
  · exact B700671
  · exact B700675
  · exact B700679
  · exact B700683
  · exact B700687
  · exact B700691
  · exact B700695
  · exact B700699
  · exact B700703
  · exact B700707
  · exact B700711
  · exact B700715
  · exact B700719
  · exact B700723
  · exact B700727
  · exact B700731
  · exact B700735
  · exact B700739
  · exact B700743
  · exact B700747
  · exact B700751
  · exact B700755
  · exact B700759
  · exact B700763
  · exact B700767
  · exact B700771
  · exact B700775
  · exact B700779
  · exact B700783
  · exact B700787
  · exact B700791
  · exact B700795
  · exact B700799
  · exact B700803
  · exact B700807
  · exact B700811
  · exact B700815
  · exact B700819
  · exact B700823
  · exact B700827
  · exact B700831
  · exact B700835
  · exact B700839
  · exact B700843
  · exact B700847
  · exact B700851
  · exact B700855
  · exact B700859
  · exact B700863
  · exact B700867
  · exact B700871
  · exact B700875
  · exact B700879
  · exact B700883
  · exact B700887
  · exact B700891
  · exact B700895
  · exact B700899
  · exact B700903
  · exact B700907
  · exact B700911
  · exact B700915
  · exact B700919
  · exact B700923
  · exact B700927
  · exact B700931
  · exact B700935
  · exact B700939
  · exact B700943
  · exact B700947
  · exact B700951
  · exact B700955
  · exact B700959
  · exact B700963
  · exact B700967
  · exact B700971
  · exact B700975
  · exact B700979
  · exact B700983
  · exact B700987
  · exact B700991
  · exact B700995
  · exact B700999
  · exact B701003
  · exact B701007
  · exact B701011
  · exact B701015
  · exact B701019
  · exact B701023
  · exact B701027
  · exact B701031
  · exact B701035
  · exact B701039
  · exact B701043
  · exact B701047
  · exact B701051
  · exact B701055
  · exact B701059
  · exact B701063
  · exact B701067
  · exact B701071
  · exact B701075
  · exact B701079
  · exact B701083
  · exact B701087
  · exact B701091
  · exact B701095
  · exact B701099
  · exact B701103
  · exact B701107
  · exact B701111
  · exact B701115

theorem C1 (j : ℕ) (h1 : 175279 ≤ j) (h2 : j ≤ 175578) : Blo 698317 (4 * j + 3) := by
  interval_cases j
  · exact B701119
  · exact B701123
  · exact B701127
  · exact B701131
  · exact B701135
  · exact B701139
  · exact B701143
  · exact B701147
  · exact B701151
  · exact B701155
  · exact B701159
  · exact B701163
  · exact B701167
  · exact B701171
  · exact B701175
  · exact B701179
  · exact B701183
  · exact B701187
  · exact B701191
  · exact B701195
  · exact B701199
  · exact B701203
  · exact B701207
  · exact B701211
  · exact B701215
  · exact B701219
  · exact B701223
  · exact B701227
  · exact B701231
  · exact B701235
  · exact B701239
  · exact B701243
  · exact B701247
  · exact B701251
  · exact B701255
  · exact B701259
  · exact B701263
  · exact B701267
  · exact B701271
  · exact B701275
  · exact B701279
  · exact B701283
  · exact B701287
  · exact B701291
  · exact B701295
  · exact B701299
  · exact B701303
  · exact B701307
  · exact B701311
  · exact B701315
  · exact B701319
  · exact B701323
  · exact B701327
  · exact B701331
  · exact B701335
  · exact B701339
  · exact B701343
  · exact B701347
  · exact B701351
  · exact B701355
  · exact B701359
  · exact B701363
  · exact B701367
  · exact B701371
  · exact B701375
  · exact B701379
  · exact B701383
  · exact B701387
  · exact B701391
  · exact B701395
  · exact B701399
  · exact B701403
  · exact B701407
  · exact B701411
  · exact B701415
  · exact B701419
  · exact B701423
  · exact B701427
  · exact B701431
  · exact B701435
  · exact B701439
  · exact B701443
  · exact B701447
  · exact B701451
  · exact B701455
  · exact B701459
  · exact B701463
  · exact B701467
  · exact B701471
  · exact B701475
  · exact B701479
  · exact B701483
  · exact B701487
  · exact B701491
  · exact B701495
  · exact B701499
  · exact B701503
  · exact B701507
  · exact B701511
  · exact B701515
  · exact B701519
  · exact B701523
  · exact B701527
  · exact B701531
  · exact B701535
  · exact B701539
  · exact B701543
  · exact B701547
  · exact B701551
  · exact B701555
  · exact B701559
  · exact B701563
  · exact B701567
  · exact B701571
  · exact B701575
  · exact B701579
  · exact B701583
  · exact B701587
  · exact B701591
  · exact B701595
  · exact B701599
  · exact B701603
  · exact B701607
  · exact B701611
  · exact B701615
  · exact B701619
  · exact B701623
  · exact B701627
  · exact B701631
  · exact B701635
  · exact B701639
  · exact B701643
  · exact B701647
  · exact B701651
  · exact B701655
  · exact B701659
  · exact B701663
  · exact B701667
  · exact B701671
  · exact B701675
  · exact B701679
  · exact B701683
  · exact B701687
  · exact B701691
  · exact B701695
  · exact B701699
  · exact B701703
  · exact B701707
  · exact B701711
  · exact B701715
  · exact B701719
  · exact B701723
  · exact B701727
  · exact B701731
  · exact B701735
  · exact B701739
  · exact B701743
  · exact B701747
  · exact B701751
  · exact B701755
  · exact B701759
  · exact B701763
  · exact B701767
  · exact B701771
  · exact B701775
  · exact B701779
  · exact B701783
  · exact B701787
  · exact B701791
  · exact B701795
  · exact B701799
  · exact B701803
  · exact B701807
  · exact B701811
  · exact B701815
  · exact B701819
  · exact B701823
  · exact B701827
  · exact B701831
  · exact B701835
  · exact B701839
  · exact B701843
  · exact B701847
  · exact B701851
  · exact B701855
  · exact B701859
  · exact B701863
  · exact B701867
  · exact B701871
  · exact B701875
  · exact B701879
  · exact B701883
  · exact B701887
  · exact B701891
  · exact B701895
  · exact B701899
  · exact B701903
  · exact B701907
  · exact B701911
  · exact B701915
  · exact B701919
  · exact B701923
  · exact B701927
  · exact B701931
  · exact B701935
  · exact B701939
  · exact B701943
  · exact B701947
  · exact B701951
  · exact B701955
  · exact B701959
  · exact B701963
  · exact B701967
  · exact B701971
  · exact B701975
  · exact B701979
  · exact B701983
  · exact B701987
  · exact B701991
  · exact B701995
  · exact B701999
  · exact B702003
  · exact B702007
  · exact B702011
  · exact B702015
  · exact B702019
  · exact B702023
  · exact B702027
  · exact B702031
  · exact B702035
  · exact B702039
  · exact B702043
  · exact B702047
  · exact B702051
  · exact B702055
  · exact B702059
  · exact B702063
  · exact B702067
  · exact B702071
  · exact B702075
  · exact B702079
  · exact B702083
  · exact B702087
  · exact B702091
  · exact B702095
  · exact B702099
  · exact B702103
  · exact B702107
  · exact B702111
  · exact B702115
  · exact B702119
  · exact B702123
  · exact B702127
  · exact B702131
  · exact B702135
  · exact B702139
  · exact B702143
  · exact B702147
  · exact B702151
  · exact B702155
  · exact B702159
  · exact B702163
  · exact B702167
  · exact B702171
  · exact B702175
  · exact B702179
  · exact B702183
  · exact B702187
  · exact B702191
  · exact B702195
  · exact B702199
  · exact B702203
  · exact B702207
  · exact B702211
  · exact B702215
  · exact B702219
  · exact B702223
  · exact B702227
  · exact B702231
  · exact B702235
  · exact B702239
  · exact B702243
  · exact B702247
  · exact B702251
  · exact B702255
  · exact B702259
  · exact B702263
  · exact B702267
  · exact B702271
  · exact B702275
  · exact B702279
  · exact B702283
  · exact B702287
  · exact B702291
  · exact B702295
  · exact B702299
  · exact B702303
  · exact B702307
  · exact B702311
  · exact B702315

theorem solution (m : ℕ) (hlo : 698317 ≤ m) (hhi : m ≤ 702317) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 174579 ≤ j := by omega
    have hj2 : j ≤ 175578 := by omega
    have hb : Blo 698317 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 175279 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
