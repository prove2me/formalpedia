-- Prove2me | solution 1 for syracuse_large_common_first_passage_families_with_prescribed_later_descent
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T11:10:55.628406+00:00
-- url     : https://prove2.me/submissions/db71492f-90f0-4f48-8dc7-150434502b26

import Mathlib
import Definitions.Def_syracuseStep

open Nat

private theorem syracuse_step_trailing_ones (l q : ℕ) (hq : 0 < q) :
    syracuseStep (2^(l+1)*q-1)=ordCompl[2] (2^l*(3*q)-1) := by
  have hpos : 0<2^l*q := Nat.mul_pos (Nat.two_pow_pos l) hq
  have hleft : 2^(l+1)*q=2*(2^l*q) := by rw [pow_succ]; ring
  have hright : 2^l*(3*q)=3*(2^l*q) := by ring
  have he : 3*(2^(l+1)*q-1)+1=2*(2^l*(3*q)-1) := by
    rw [hleft,hright]
    omega
  unfold syracuseStep
  rw [he]
  exact Nat.ordCompl_self_pow_mul _ 1 Nat.prime_two

private theorem odd_part_trailing_ones (l q : ℕ) (hq : 0<q) :
    ordCompl[2] (2^(l+1)*q-1)=2^(l+1)*q-1 := by
  apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr
  apply Or.inr
  rw [Nat.dvd_iff_mod_eq_zero]
  have hpos : 0<2^l*q := Nat.mul_pos (Nat.two_pow_pos l) hq
  have hp : 2^(l+1)*q=2*(2^l*q) := by rw [pow_succ]; ring
  omega

/-- The accelerated map absorbs the terminal halving segment in the
last step of a prescribed odd run. -/
theorem syracuse_prescribed_odd_run_exact (L q : ℕ) (hL : 0<L) (hq : 0<q) :
    syracuseStep^[L] (2^L*q-1)=ordCompl[2] (3^L*q-1) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  clear hL
  induction l generalizing q with
  | zero =>
    simpa using syracuse_step_trailing_ones 0 q hq
  | succ l ih =>
    have hh : 3^(l+1)*(3*q)=3^l.succ.succ*q := by
      simp only [Nat.succ_eq_add_one,pow_succ]
      ring
    rw [Function.iterate_succ_apply,syracuse_step_trailing_ones (l+1) q hq,
      odd_part_trailing_ones l (3*q) (by omega),ih (3*q) (by omega),hh]

/-- The first maximal odd run is determined by the valuation of
`n + 1`. Its Syracuse endpoint is the odd part of the shortcut peak. -/
theorem syracuse_maximal_odd_run_exact (n : ℕ) (hodd : n%2=1) :
    let L := (n+1).factorization 2
    let q := (n+1)/2^L
    syracuseStep^[L] n=ordCompl[2] (3^L*q-1) := by
  let L := (n+1).factorization 2
  let q := (n+1)/2^L
  change syracuseStep^[L] n=ordCompl[2] (3^L*q-1)
  have hd : 2∣n+1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hL : 0<L := (Nat.prime_two.dvd_iff_one_le_factorization (Nat.succ_ne_zero n)).mp hd
  have hx : 2^L*q=n+1 := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hq : 0<q := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz,mul_zero] at hx
    omega
  conv_lhs => rw [show n=2^L*q-1 by omega]
  exact syracuse_prescribed_odd_run_exact L q hL hq

private theorem syracuse_prescribed_odd_run_prefix (L q i : ℕ)
    (hq : 0<q) (hi : i<L) :
    syracuseStep^[i] (2^L*q-1)=3^i*(2^(L-i)*q)-1 := by
  cases i with
  | zero => simp
  | succ i =>
    have hf : 2^L*q=2^(i+1)*(2^(L-(i+1))*q) := by
      rw [←Nat.mul_assoc,←pow_add,show i+1+(L-(i+1))=L by omega]
    have hpos : 0<2^(L-(i+1))*q := Nat.mul_pos (Nat.two_pow_pos _) hq
    have hterm := syracuse_prescribed_odd_run_exact (i+1) (2^(L-(i+1))*q) (by omega) hpos
    rw [←hf] at hterm
    rw [hterm]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show L-(i+1)≠0 by omega)
    have he : 3^(i+1)*(2^(L-(i+1))*q)=2^(j+1)*(3^(i+1)*q) := by
      rw [hj,Nat.succ_eq_add_one]
      ring
    rw [he,odd_part_trailing_ones j _ (Nat.mul_pos (Nat.pow_pos (by decide)) hq)]

private theorem syracuse_prescribed_odd_run_no_early_descent (L q i : ℕ)
    (hq : 0<q) (hi : i<L) : 2^L*q-1≤ syracuseStep^[i] (2^L*q-1) := by
  rw [syracuse_prescribed_odd_run_prefix L q i hq hi]
  apply Nat.sub_le_sub_right
  calc
    _ = 2^i*(2^(L-i)*q) := by rw [←Nat.mul_assoc,←pow_add,Nat.add_sub_of_le hi.le]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)

/-- A strict quotient bound for a divisible power of two is an exact
criterion for descent at the end of the prescribed odd run. -/
theorem syracuse_prescribed_odd_run_exit_iff (L q : ℕ) (hL : 0<L) (hq : 0<q) :
    let x := 2^L*q-1
    let w := 3^L*q-1
    syracuseStep^[L] x<x ↔ ∃ s : ℕ, 2^s∣w ∧ w<2^s*x := by
  dsimp only
  rw [syracuse_prescribed_odd_run_exact L q hL hq]
  let w := 3^L*q-1
  let x := 2^L*q-1
  change ordCompl[2] w<x ↔ ∃ s : ℕ, 2^s∣w ∧ w<2^s*x
  constructor
  · intro h
    let s := w.factorization 2
    have hd : 2^s*(ordCompl[2] w)=w := Nat.ordProj_mul_ordCompl_eq_self _ _
    exact ⟨s,⟨_,hd.symm⟩,hd ▸ Nat.mul_lt_mul_of_pos_left h (Nat.two_pow_pos s)⟩
  · rintro ⟨s,hs,hbound⟩
    have hquot : w/2^s<x := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).mpr
      (by simpa only [Nat.mul_comm] using hbound)
    rw [←Nat.ordCompl_div_pow_of_dvd s Nat.prime_two hs]
    exact (Nat.div_le_self _ _).trans_lt hquot

private theorem odd_run_exit_gap (L : ℕ) (hL : 2≤L) :
    (3:ℕ)^L+2^L≤2^L*2^L := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hL
  clear hL
  induction d with
  | zero => decide
  | succ d ih =>
    have hindex : 2+d.succ=(2+d)+1 := by omega
    rw [hindex,pow_succ (3:ℕ),pow_succ (2:ℕ)]
    calc
      _ ≤ 4*((3:ℕ)^(2+d)+2^(2+d)) := by omega
      _ ≤ 4*(2^(2+d)*2^(2+d)) := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

/-- At least `L` further halvings after the shortcut ascent guarantee
that the first strict Syracuse descent occurs at clock `L`. -/
theorem syracuse_first_descent_from_long_odd_run (L q : ℕ)
    (hL : 2≤L) (hq : 0<q) (hdiv : 2^L∣3^L*q-1) :
    (∀ i<L, 2^L*q-1≤ syracuseStep^[i] (2^L*q-1)) ∧
      syracuseStep^[L] (2^L*q-1)<2^L*q-1 := by
  refine ⟨fun i hi => syracuse_prescribed_odd_run_no_early_descent L q i hq hi,?_⟩
  apply (syracuse_prescribed_odd_run_exit_iff L q (by omega) hq).mpr
  refine ⟨L,hdiv,?_⟩
  have hm := Nat.mul_le_mul_right q (odd_run_exit_gap L hL)
  rw [Nat.add_mul] at hm
  have hp : 2^L≤2^L*q := Nat.le_mul_of_pos_right _ hq
  have hc : 2^L*(2^L*q-1)+2^L=2^L*2^L*q := calc
    _ = 2^L*((2^L*q-1)+1) := by rw [Nat.mul_add,mul_one]
    _ = _ := by rw [Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos L) hq)]; ring
  have hz : 0<3^L*q := Nat.mul_pos (Nat.pow_pos (by decide)) hq
  omega



private theorem predecessor_at (a e : ℕ) (ha : 1 < a) (ho : a%2 = 1)
    (he : 2 ≤ e) (he' : e ≤ 7)
    (hmod : (2^e*a)%3 = 1) (hmod' : (2^e*a)%9 ≠ 1) :
    let b := (2^e*a-1)/3
    a < b ∧ b ≤ 43*a ∧ b%2 = 1 ∧ ¬ 3∣b ∧ syracuseStep b = a := by
  dsimp only
  let b := (2^e*a-1)/3
  have hlo := Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by decide : 0 < 2) he)
  have hhi := Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by decide : 0 < 2) he')
  norm_num at hlo hhi
  have hdiv : 3*b+1 = 2^e*a := by dsimp [b]; omega
  have hEven : 2 ∣ 2^e*a := (dvd_pow_self _ (by omega : e ≠ 0)).trans (dvd_mul_right _ _)
  have hg : syracuseStep b = a := by
    rw [syracuseStep, hdiv]
    exact Nat.ordCompl_pow_mul_of_not_dvd e Nat.prime_two (by omega)
  have hb : b%2 = 1 := by omega
  have hb3 : ¬ 3 ∣ b := by omega
  exact ⟨by omega, by omega, hb, hb3, hg⟩

private theorem two_predecessors (a : ℕ) (ha : 1 < a) (ho : a%2 = 1) (h3 : ¬ 3 ∣ a) :
    ∃ b c : ℕ, b < c ∧
      (a < b ∧ b ≤ 43*a ∧ b%2 = 1 ∧ ¬ 3∣b ∧ syracuseStep b = a) ∧
      (a < c ∧ c ≤ 43*a ∧ c%2 = 1 ∧ ¬ 3∣c ∧ syracuseStep c = a) := by
  obtain ⟨e,f,he,hef,hf,hem,hen,hfm,hfn⟩ :
      ∃ e f : ℕ, 2 ≤ e ∧ e < f ∧ f ≤ 7 ∧ (2^e*a)%3 = 1 ∧ (2^e*a)%9 ≠ 1 ∧
        (2^f*a)%3 = 1 ∧ (2^f*a)%9 ≠ 1 := by
    have hcases : a%9=1 ∨ a%9=2 ∨ a%9=4 ∨ a%9=5 ∨ a%9=7 ∨ a%9=8 := by omega
    rcases hcases with h|h|h|h|h|h
    · refine ⟨2,4,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨3,7,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨2,6,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨3,5,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨4,6,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨5,7,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
  let b := (2^e*a-1)/3
  let c := (2^f*a-1)/3
  have hb := predecessor_at a e ha ho he (by omega) hem hen
  have hc := predecessor_at a f ha ho (by omega) hf hfm hfn
  have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) hef
  have hprod := Nat.mul_lt_mul_of_pos_right hpow (by omega : 0 < a)
  have hbexact : 3*b+1 = 2^e*a := by dsimp [b]; omega
  have hcexact : 3*c+1 = 2^f*a := by dsimp [c]; omega
  refine ⟨b,c,?_,hb,hc⟩
  omega

private theorem large_coprime_ancestors (a d : ℕ)
    (ha : 1 < a) (ho : a%2 = 1) (h3 : ¬ 3 ∣ a) :
    ∃ S : Finset ℕ, S.card = 2^d ∧ ∀ b ∈ S,
      b ≤ 43^d*a ∧ b%2 = 1 ∧ ¬ 3 ∣ b ∧
      syracuseStep^[d] b = a ∧ ∀ i ≤ d, a ≤ syracuseStep^[i] b := by
  classical
  induction d with
  | zero =>
    refine ⟨{a}, by simp, ?_⟩
    intro b hb
    have heq : b = a := Finset.mem_singleton.mp hb
    subst b
    simp [ho, h3]
  | succ d ih =>
    obtain ⟨S,hcard,hS⟩ := ih
    have hChildren (p : {p // p ∈ S}) := by
      obtain ⟨_,hodd, hnot3,_,hfloor⟩ := hS p p.property
      have hp : a ≤ p := by simpa using hfloor 0 (Nat.zero_le _)
      exact two_predecessors p (ha.trans_le hp) hodd hnot3
    choose l u hlt hl hu using hChildren
    let f (w : Bool × {p // p ∈ S}) := if w.1 then u w.2 else l w.2
    have hp (w : Bool × {p // p ∈ S}) :
        (w.2 : ℕ) < f w ∧ f w ≤ 43*w.2 ∧
          f w%2 = 1 ∧ ¬ 3∣f w ∧ syracuseStep (f w) = w.2 := by
      rcases w with ⟨b,p⟩
      cases b
      · simpa [f] using hl p
      · simpa [f] using hu p
    have hf : Function.Injective f := by
      rintro ⟨b,p⟩ ⟨c,q⟩ h
      have heq : p = q := by
        apply Subtype.ext
        exact (hp (b,p)).2.2.2.2.symm.trans ((congrArg syracuseStep h).trans (hp (c,q)).2.2.2.2)
      subst q
      cases b <;> cases c <;> try rfl
      · exact False.elim ((Nat.ne_of_lt (hlt p)) (by simpa [f] using h))
      · exact False.elim ((Nat.ne_of_lt (hlt p)) (by simpa [f] using h.symm))
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, Fintype.card_coe, hcard, pow_succ, Nat.mul_comm]
    · intro b hb
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hb,hle,hOdd,hThree,heq⟩ := hp w
      obtain ⟨hP,_,_,hvisit,hfloor⟩ := hS w.2 w.2.property
      refine ⟨?_,hOdd,hThree,?_,?_⟩
      · calc
          f w ≤ 43 * (w.2 : ℕ) := hle
          _ ≤ 43 * (43^d*a) := Nat.mul_le_mul_left _ hP
          _ = 43^(d+1)*a := by rw [_root_.pow_succ']; ac_rfl
      · rwa [Function.iterate_succ_apply,heq]
      · intro i hi
        cases i with
        | zero =>
          have hP0 : a ≤ (w.2 : ℕ) := by simpa using hfloor 0 (Nat.zero_le _)
          exact hP0.trans hb.le
        | succ i =>
          rw [Function.iterate_succ_apply,heq]
          exact hfloor i (by omega)


private theorem predecessor_above_twice_barrier (a B : ℕ)
    (hB : 1 < B) (hBa : B ≤ a) (hOdd : a%2 = 1) (hThree : ¬ 3 ∣ a) :
    ∃ c : ℕ, 2*B ≤ c ∧ c ≤ 43*a ∧ c%2 = 1 ∧ ¬ 3 ∣ c ∧ syracuseStep c = a := by
  obtain ⟨e, he, he', he3, he9⟩ :
      ∃ e : ℕ, 3 ≤ e ∧ e ≤ 7 ∧ (2^e*a)%3 = 1 ∧ (2^e*a)%9 ≠ 1 := by
    have hcases : a%9=1 ∨ a%9=2 ∨ a%9=4 ∨ a%9=5 ∨ a%9=7 ∨ a%9=8 := by omega
    rcases hcases with h|h|h|h|h|h
    · refine ⟨4,by decide,by decide,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨3,by decide,by decide,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨6,by decide,by decide,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨3,by decide,by decide,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨4,by decide,by decide,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨5,by decide,by decide,?_,?_⟩ <;> norm_num <;> omega
  let c := (2^e*a-1)/3
  obtain ⟨_,hUp,ho,h3,hstep⟩ := predecessor_at a e (hB.trans_le hBa) hOdd (by omega) he' he3 he9
  have hl := Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by decide : 0 < 2) he)
  norm_num at hl
  refine ⟨c,?_,hUp,ho,h3,hstep⟩
  change 2*B ≤ (2^e*a-1)/3
  omega

theorem syracuse_common_first_passage_family_for_any_unit_target (a B d : ℕ)
    (hB : 1 < B) (hLow : B ≤ a) (hUpper : 2*a+2 ≤ 3*B)
    (hOdd : a%2 = 1) (hThree : ¬ 3 ∣ a) :
    ∃ S : Finset ℕ, S.card = 2^d ∧
      ∀ b ∈ S, 2*b ≤ 3*43^(d+1)*B ∧ b%2 = 1 ∧ ¬ 3 ∣ b ∧
        syracuseStep^[d+1] b = a ∧ ∀ i ≤ d, 2*B ≤ syracuseStep^[i] b := by
  obtain ⟨c,hC,hCsize,hCodd,hCthree,hCstep⟩ :=
    predecessor_above_twice_barrier a B hB hLow hOdd hThree
  obtain ⟨S,hCard,hS⟩ := large_coprime_ancestors c d (by omega) hCodd hCthree
  refine ⟨S,hCard,?_⟩
  intro b hb
  obtain ⟨hSize,hOdd',hThree',hRoot,hFloor⟩ := hS b hb
  refine ⟨?_,hOdd',hThree',?_,?_⟩
  · calc
      2*b ≤ 2*(43^d*c) := Nat.mul_le_mul_left _ hSize
      _ ≤ 2*(43^d*(43*a)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hCsize)
      _ = 43^(d+1)*(2*a) := by rw [pow_succ]; ac_rfl
      _ ≤ 43^(d+1)*(3*B) := Nat.mul_le_mul_left _ (by omega)
      _ = 3*43^(d+1)*B := by ac_rfl
  · rw [Function.iterate_succ_apply',hRoot,hCstep]
  · intro i hi
    exact hC.trans (hFloor i hi)


private theorem large_coprime_with_exact_first_descent (L N : ℕ) (hL : 2 ≤ L) :
    ∃ a : ℕ, N < a ∧ a%12=11 ∧
      (∀ i<L, a ≤ syracuseStep^[i] a) ∧ syracuseStep^[L] a < a := by
  let m := 2^L
  let p := 3^(L+1)
  have hcop : m.Coprime p := ((show Nat.Coprime 2 3 by decide).pow_left _).pow_right _
  obtain ⟨r,hr2,hr3⟩ := Nat.chineseRemainder hcop 1 0
  let u := m*(N+2)
  let y := r+p*u
  have hp : 0<p := Nat.pow_pos (by decide)
  have hm : m∣p*u := ⟨p*(N+2),by dsimp [u]; ring⟩
  have h2y : y ≡ 1 [MOD m] := by
    simpa [y] using hr2.add (Nat.modEq_zero_iff_dvd.mpr hm)
  have h3y : p∣y := dvd_add (Nat.modEq_zero_iff_dvd.mp hr3) (dvd_mul_right _ _)
  obtain ⟨q,hq⟩ := h3y
  have hpu : p*u≤p*q := by
    rw [←hq]
    dsimp [y]
    omega
  have hu := Nat.le_of_mul_le_mul_left hpu hp
  have hfloor : N+2≤u := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos L)
  have hqpos : 0<q := by omega
  have hy : 0<y := by rw [hq]; exact Nat.mul_pos hp hqpos
  have hy' : (y-1)+1=y := Nat.sub_add_cancel hy
  have hd : m∣y-1 := Nat.modEq_zero_iff_dvd.mp
    (Nat.ModEq.add_right_cancel' 1 (by simpa only [hy',zero_add] using h2y))
  have hFactor : y = 3^L*(3*q) := by rw [hq]; dsimp [p]; rw [pow_succ]; ring
  rw [hFactor] at hd
  obtain ⟨hpre,hdes⟩ := syracuse_first_descent_from_long_odd_run L (3*q) hL (by omega) hd
  let a := 2^L*(3*q)-1
  have hsize : 3*q ≤ 2^L*(3*q) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hmod : 12 ∣ 2^L*(3*q) := by
    have hdiv : 2^2 ∣ 2^L := pow_dvd_pow _ hL
    obtain ⟨w,hw⟩ := hdiv
    norm_num at hw
    refine ⟨w*q,?_⟩
    rw [hw]
    ring
  refine ⟨a,?_,?_,hpre,hdes⟩ <;> dsimp [a] <;> omega

theorem solution
    (L d N : ℕ) (hL : 2 ≤ L) :
    ∃ B : ℕ, N < B ∧ 1 < B ∧ B%12=11 ∧ ∃ S : Finset ℕ, S.card=2^d ∧
      ∀ b ∈ S, 2*b ≤ 3*43^(d+1)*B ∧ b%2=1 ∧ ¬ 3 ∣ b ∧
        syracuseStep^[d+1] b = B ∧
        (∀ i ≤ d, 2*B ≤ syracuseStep^[i] b) ∧
        (∀ i < L, B ≤ syracuseStep^[i+(d+1)] b) ∧
        syracuseStep^[L+(d+1)] b < B := by
  obtain ⟨B,hN,hr,hpre,hdes⟩ := large_coprime_with_exact_first_descent L (N+2) hL
  obtain ⟨S,hCard,hS⟩ := syracuse_common_first_passage_family_for_any_unit_target B B d
    (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨B,by omega,by omega,hr,S,hCard,?_⟩
  intro b hb
  obtain ⟨hX,ho,h3,hEnd,hBefore⟩ := hS b hb
  refine ⟨hX,ho,h3,hEnd,hBefore,?_,?_⟩
  · intro i hi
    rw [Function.iterate_add_apply,hEnd]
    exact hpre i hi
  · rwa [Function.iterate_add_apply,hEnd]
