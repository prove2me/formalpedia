-- Prove2me | solution 1 for syracuse_return_79335_minimum_in_five_row_window
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:59:50.40221+00:00
-- url     : https://prove2.me/submissions/c9d228d6-2016-4d29-89f0-fe75e424df1c

import Mathlib
import Theorems.Thm_syracuse_nontrivial_period_coordinates_at_1241513984
import Theorems.Thm_syracuse_no_cycle_below_1241513984
import Theorems.Thm_syracuse_periodic_reaches_one

open scoped BigOperators

private abbrev l2 : ℝ := 0.6931471805599453093
private abbrev u2 : ℝ := 0.6931471805599453095
private abbrev l3 : ℝ := 1.0986122886681096913
private abbrev u3 : ℝ := 1.0986122886681096915

set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
private theorem log_bounds :
    l2 < Real.log 2 ∧ Real.log 2 < u2 ∧ l3 < Real.log 3 ∧ Real.log 3 < u3 := by
  have ha := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/3) (by norm_num) 40
  have hb := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/4) (by norm_num) 40
  rw [show 1 - (1:ℝ)/3 = ((3:ℝ)/2)⁻¹ by norm_num, Real.log_inv] at ha
  rw [show 1 - (1:ℝ)/4 = ((4:ℝ)/3)⁻¹ by norm_num, Real.log_inv] at hb
  norm_num [Finset.sum_range_succ] at ha hb
  obtain ⟨ha1,ha2⟩ := abs_le.mp ha
  obtain ⟨hb1,hb2⟩ := abs_le.mp hb
  have h2 : Real.log 2 = Real.log (3/2)+Real.log (4/3) := by
    rw [← Real.log_mul (by norm_num : (3:ℝ)/2 ≠ 0) (by norm_num : (4:ℝ)/3 ≠ 0)]
    norm_num
  have h3 : Real.log 3 = 2*Real.log (3/2)+Real.log (4/3) := by
    rw [show (3:ℝ) = ((3:ℝ)/2)^2*((4:ℝ)/3) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  unfold l2 u2 l3 u3
  constructor
  · linarith only [ha1,ha2,hb1,hb2,h2]
  constructor
  · linarith only [ha1,ha2,hb1,hb2,h2]
  constructor
  · linarith only [ha1,ha2,hb1,hb2,h3]
  · linarith only [ha1,ha2,hb1,hb2,h3]


private def smallExponent (w : Fin 4 → Fin 3) (i : ℕ) : ℕ :=
  if h : i < 4 then (w ⟨i,h⟩).val+1 else 1

private def rate (w : Fin 4 → Fin 3) : ℕ → ℚ
  | 0 => 1
  | i+1 => rate w i * (3/(2^smallExponent w i))

/- An exact check of the eighty-one possible words with four exponents
between one and three. -/
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem rate_certificate (w : Fin 4 → Fin 3) :
    ∃ j : Fin 5, (∑ i ∈ Finset.range 5, rate w j.val / rate w i) ≤ 319/81 := by
  revert w
  decide +kernel

private theorem reciprocal_of_cross_bound (B x l q : ℕ) (hB : 0 < B) (hx : 0 < x)
    (hl : 0 < l) (h : l*B ≤ q*x) :
    (1:ℝ)/(x:ℝ) ≤ (q:ℝ)/((l:ℝ)*(B:ℝ)) := by
  have hxp : (0:ℝ)<x := by exact_mod_cast hx
  have hBp : (0:ℝ)<B := by exact_mod_cast hB
  have hlp : (0:ℝ)<l := by exact_mod_cast hl
  apply (div_le_div_iff₀ hxp (mul_pos hlp hBp)).mpr
  simpa only [one_mul] using (show (l:ℝ)*B ≤ (q:ℝ)*x by exact_mod_cast h)

private theorem pair_has_large (B u v a : ℕ) (hB : 2000 ≤ B) (hu : B ≤ u) (hv : B ≤ v)
    (ha : 0 < a) (he : 2^a*v = 3*u+1) : 33*B ≤ 25*u ∨ 33*B ≤ 25*v := by
  by_cases h : a = 1
  · right
    rw [h] at he
    norm_num only [pow_one] at he
    omega
  · left
    have h4 : 4 ≤ 2^a := by
      calc
        4 = (2:ℕ)^2 := by decide
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    have hh : 4*B ≤ 3*u+1 := by
      rw [← he]
      exact Nat.mul_le_mul h4 hv
    omega

private theorem high_predecessor (B u v a : ℕ) (hB : 2000 ≤ B) (hv : B ≤ v)
    (ha : 4 ≤ a) (he : 2^a*v = 3*u+1) : 53*B ≤ 10*u := by
  have h16 : 16 ≤ 2^a := by
    calc
      16 = (2:ℕ)^4 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) ha
  have hh : 16*B ≤ 3*u+1 := by
    rw [← he]
    exact Nat.mul_le_mul h16 hv
  omega

private theorem five_high (B : ℕ) (x e : ℕ → ℕ) (hB : 2000 ≤ B)
    (hfloor : ∀ i < 5, B ≤ x i) (hpos : ∀ i < 4, 0 < e i)
    (hstep : ∀ i < 4, 2^(e i)*x (i+1) = 3*x i+1)
    (q : ℕ) (hq : q < 4) (hEq : 4 ≤ e q) :
    (∑ i ∈ Finset.range 5, (1:ℝ)/(x i:ℝ)) ≤ 79/(20*(B:ℝ)) := by
  classical
  have hBp : 0 < B := by omega
  have hBr : (0:ℝ)<B := by exact_mod_cast hBp
  have hq5 : q < 5 := by omega
  have hqv := high_predecessor B (x q) (x (q+1)) (e q) hB
    (hfloor (q+1) (by omega)) hEq (hstep q hq)
  obtain ⟨r,hr,hrq,hrv⟩ : ∃ r < 5, r ≠ q ∧ 33*B ≤ 25*x r := by
    by_cases hq2 : q < 2
    · rcases pair_has_large B (x 3) (x 4) (e 3) hB (hfloor _ (by decide)) (hfloor _ (by decide))
        (hpos _ (by decide)) (hstep _ (by decide)) with h | h
      · exact ⟨3,by decide,by omega,h⟩
      · exact ⟨4,by decide,by omega,h⟩
    · rcases pair_has_large B (x 0) (x 1) (e 0) hB (hfloor _ (by decide)) (hfloor _ (by decide))
        (hpos _ (by decide)) (hstep _ (by decide)) with h | h
      · exact ⟨0,by decide,by omega,h⟩
      · exact ⟨1,by decide,by omega,h⟩
  let a : ℝ := 1/(B:ℝ)
  let b : ℝ := 10/(53*(B:ℝ))
  let c : ℝ := 25/(33*(B:ℝ))
  have hW : ∀ i < 5, (1:ℝ)/(x i:ℝ) ≤
      a-(if i=q then a-b else 0)-(if i=r then a-c else 0) := by
    intro i hi
    have hx := hBp.trans_le (hfloor i hi)
    by_cases hiq : i=q
    · subst i
      simp [if_neg (Ne.symm hrq)]
      have hb := reciprocal_of_cross_bound B (x q) 53 10 hBp hx (by decide) hqv
      change (1:ℝ)/(x q:ℝ) ≤ b at hb
      simpa only [one_div] using hb
    · by_cases hir : i=r
      · subst i
        simp [if_neg hrq]
        have hc := reciprocal_of_cross_bound B (x r) 33 25 hBp hx (by decide) hrv
        change (1:ℝ)/(x r:ℝ) ≤ c at hc
        simpa only [one_div] using hc
      · simp only [if_neg hiq,if_neg hir,sub_zero]
        exact one_div_le_one_div_of_le hBr (by exact_mod_cast hfloor i hi)
  calc
    _ ≤ ∑ i ∈ Finset.range 5, (a-(if i=q then a-b else 0)-(if i=r then a-c else 0)) :=
      Finset.sum_le_sum (fun i hi => hW i (Finset.mem_range.mp hi))
    _ = 3*a+b+c := by
      simp [Finset.sum_sub_distrib, Finset.mem_range.mpr hq5, Finset.mem_range.mpr hr]
      ring
    _ ≤ _ := by dsimp [a,b,c]; field_simp [hBr.ne']; norm_num

private theorem five_low (B : ℕ) (x e : ℕ → ℕ) (hB : 2000 ≤ B)
    (hfloor : ∀ i < 5, B ≤ x i) (hpos : ∀ i < 4, 0 < e i)
    (hstep : ∀ i < 4, 2^(e i)*x (i+1) = 3*x i+1) (hsmall : ∀ i < 4, e i ≤ 3) :
    (∑ i ∈ Finset.range 5, (1:ℝ)/(x i:ℝ)) ≤ 79/(20*(B:ℝ)) := by
  let w : Fin 4 → Fin 3 := fun i => ⟨e i.val-1, by have h:=hsmall i.val i.isLt; omega⟩
  let R (i : ℕ) : ℝ := (rate w i:ℝ)
  have hR (i : ℕ) : 0 < R i := by
    induction i with
    | zero => norm_num [R,rate]
    | succ i ih =>
      have heq : R (i+1) = R i*((3:ℝ)/(2^smallExponent w i)) := by
        simp [R,rate,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
      rw [heq]
      positivity
  have hE (i : ℕ) (hi : i < 4) : smallExponent w i = e i := by
    have hh := hpos i hi
    simp only [smallExponent,dif_pos hi,w]
    omega
  have hRS (i : ℕ) (hi : i < 4) : R (i+1)=R i*((3:ℝ)/(2^e i)) := by
    have heq : R (i+1) = R i*((3:ℝ)/(2^smallExponent w i)) := by
      simp [R,rate,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
    rw [heq,hE i hi]
  let err (i : ℕ) : ℝ := (3/2:ℝ)^i - 1
  have hBounds (i : ℕ) (hi : i ≤ 4) :
      R i*(x 0:ℝ) ≤ (x i:ℝ) ∧ (x i:ℝ) ≤ R i*(x 0:ℝ)+err i := by
    induction i with
    | zero => norm_num [R,rate,err]
    | succ i ih =>
      have hi4 : i < 4 := by omega
      obtain ⟨hlo,hhi⟩ := ih (by omega)
      let d : ℝ := 2^e i
      have hdp : 0 < d := by dsimp [d]; positivity
      have hd2 : (2:ℝ)≤d := by
        have hnat : 2 ≤ 2^e i := by
          have hh := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤e i from hpos i hi4)
          simpa using hh
        change (2:ℝ) ≤ (2:ℝ)^e i
        exact_mod_cast hnat
      have heq : (x (i+1):ℝ) = (3/d)*(x i:ℝ)+1/d := by
        have hcast : d * (x (i+1):ℝ) = 3*(x i:ℝ)+1 := by
          change (2:ℝ)^e i * (x (i+1):ℝ) = 3*(x i:ℝ)+1
          exact_mod_cast hstep i hi4
        calc
          _ = (3*(x i:ℝ)+1)/d := (eq_div_iff hdp.ne').mpr (by simpa [mul_comm] using hcast)
          _ = _ := by ring
      have hRate : R (i+1) = R i*(3/d) := hRS i hi4
      rw [hRate,heq]
      have hp : 0 ≤ 3/d := by positivity
      constructor
      · calc
          _ = (3/d)*(R i*(x 0:ℝ)) := by ring
          _ ≤ (3/d)*(x i:ℝ) := mul_le_mul_of_nonneg_left hlo hp
          _ ≤ _ := le_add_of_nonneg_right (by positivity)
      · have herr : 0 ≤ err i := by
          dsimp [err]
          exact sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2))
        have hr : (3:ℝ)/d ≤ 3/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd2
        have hinv : (1:ℝ)/d ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hd2
        calc
          _ ≤ (3/d)*(R i*(x 0:ℝ)+err i)+1/d :=
            add_le_add (mul_le_mul_of_nonneg_left hhi hp) le_rfl
          _ = (R i*(3/d))*(x 0:ℝ)+(3/d)*err i+1/d := by ring
          _ ≤ (R i*(3/d))*(x 0:ℝ)+(3/2)*err i+1/2 :=
            add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hr herr)) hinv
          _ = _ := by dsimp [err]; rw [pow_succ]; ring
  obtain ⟨j,hj⟩ := rate_certificate w
  have hcap (i : ℕ) (hi : i ≤ 4) : err i ≤ 5 := by
    dsimp [err]
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3/2) hi
    norm_num at h
    linarith only [h]
  have hfloorj : ((B:ℝ)-5) ≤ R j.val*(x 0:ℝ) := by
    have hBv : (B:ℝ) ≤ x j.val := by exact_mod_cast hfloor j.val j.isLt
    have hj' : j.val ≤ 4 := by omega
    linarith only [hBv,(hBounds j.val hj').2,hcap j.val hj']
  have hBReal : (2000:ℝ)≤B := by exact_mod_cast hB
  have hBp : (0:ℝ) < (B:ℝ)-5 := by linarith only [hBReal]
  have hRec (i : ℕ) (hi : i < 5) :
      (1:ℝ)/(x i:ℝ) ≤ (1/((B:ℝ)-5))*(R j.val/R i) := by
    have hx : (0:ℝ)<x i := by
      have hz := hfloor i hi
      exact_mod_cast (show 0<x i by omega)
    have hbase : ((B:ℝ)-5)/R j.val ≤ (x 0:ℝ) := (div_le_iff₀ (hR _)).mpr (by simpa [mul_comm] using hfloorj)
    have hxi : R i*(((B:ℝ)-5)/R j.val) ≤ x i :=
      (mul_le_mul_of_nonneg_left hbase (hR _).le).trans (hBounds i (by omega)).1
    have hiPos : 0 < R i*(((B:ℝ)-5)/R j.val) := mul_pos (hR i) (div_pos hBp (hR j.val))
    calc
      _ ≤ 1/(R i*(((B:ℝ)-5)/R j.val)) := one_div_le_one_div_of_le hiPos hxi
      _ = _ := by field_simp [(hR i).ne',(hR j.val).ne',hBp.ne']
  have hSum : (∑ i ∈ Finset.range 5, R j.val/R i) ≤ (319:ℝ)/81 := by
    unfold R
    have hcast := (Rat.cast_le (K := ℝ)).2 hj
    push_cast at hcast
    exact hcast
  calc
    _ ≤ ∑ i ∈ Finset.range 5, (1/((B:ℝ)-5))*(R j.val/R i) :=
      Finset.sum_le_sum (fun i hi => hRec i (Finset.mem_range.mp hi))
    _ = (1/((B:ℝ)-5))*(∑ i ∈ Finset.range 5, R j.val/R i) := (Finset.mul_sum _ _ _).symm
    _ ≤ (1/((B:ℝ)-5))*((319:ℝ)/81) := mul_le_mul_of_nonneg_left hSum (by positivity)
    _ ≤ _ := by field_simp [hBp,show (0:ℝ)<(B:ℝ) by linarith only [hBReal]]; linarith only [hBReal]

/-- Uniform upper bound on the sum of five reciprocals along exact odd-map rows. -/
theorem five_row_reciprocal_budget (B : ℕ) (x e : ℕ → ℕ) (hB : 2000 ≤ B)
    (hfloor : ∀ i < 5, B ≤ x i) (hpos : ∀ i < 4, 0 < e i)
    (hstep : ∀ i < 4, 2^(e i)*x (i+1) = 3*x i+1) :
    (∑ i ∈ Finset.range 5, (1:ℝ)/(x i:ℝ)) ≤ 79/(20*(B:ℝ)) := by
  by_cases h : ∃ i < 4, 4 ≤ e i
  · obtain ⟨i,hi,h4⟩ := h
    exact five_high B x e hB hfloor hpos hstep i hi h4
  · refine five_low B x e hB hfloor hpos hstep ?_
    intro i hi
    exact Nat.le_of_not_gt (fun hh => h ⟨i,hi,hh⟩)


private theorem product_le_exp_reciprocal_sum (n k : ℕ) (hn : 0 < n) :
    (2:ℝ)^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
      (syracuseStep^[k] n : ℝ) ≤
      (3:ℝ)^k*(n:ℝ)*Real.exp ((∑ i ∈ Finset.range k, 1/(syracuseStep^[i] n:ℝ))/3) := by
  let x (i : ℕ) := syracuseStep^[i] n
  let A (i : ℕ) := (Finset.range i).sum fun j => (3*x j+1).factorization 2
  let w (i : ℕ) : ℝ := 1/(x i:ℝ)
  let H (i : ℕ) := ∑ j ∈ Finset.range i, w j
  change (2:ℝ)^(A k)*(x k:ℝ) ≤ 3^k*(n:ℝ)*Real.exp (H k/3)
  induction k with
  | zero => simp [x,A,H]
  | succ k ih =>
    let a := (3*x k+1).factorization 2
    have hA : A (k+1) = A k+a := Finset.sum_range_succ _ _
    have hH : H (k+1) = H k+w k := Finset.sum_range_succ _ _
    have hrow : 2^a*x (k+1) = 3*x k+1 := by
      have hx : x (k+1) = syracuseStep (x k) := Function.iterate_succ_apply' _ _ _
      rw [hx]
      exact Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcast : (2:ℝ)^a*(x (k+1):ℝ) = 3*(x k:ℝ)+1 := by exact_mod_cast hrow
    have hx : (0:ℝ) < x k := by
      have h : 0 < x k := by
        cases k with
        | zero => exact hn
        | succ j =>
          change 0 < syracuseStep^[j+1] n
          rw [Function.iterate_succ_apply']
          exact Nat.ordCompl_pos 2 (by omega)
      exact_mod_cast h
    have hmul : 3+w k ≤ 3*Real.exp (w k/3) := by
      have h := Real.add_one_le_exp (w k/3)
      linarith
    rw [hA, pow_add, mul_assoc,hcast,hH,add_div,Real.exp_add,pow_succ]
    calc
      _ = ((2:ℝ)^(A k)*(x k:ℝ))*(3+w k) := by
        dsimp [w]
        field_simp [hx.ne']
      _ ≤ ((2:ℝ)^(A k)*(x k:ℝ))*(3*Real.exp (w k/3)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      _ ≤ (3^k*(n:ℝ)*Real.exp (H k/3))*(3*Real.exp (w k/3)) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by ring


private theorem first_coordinate_unique (p a b : ℕ)
    (hp : p = 79335) (ha : 0 < a) (hb : 0 < b)
    (he : p = 31867*a+47468*b) : a=1 ∧ b=1 := by
  constructor
  · by_contra hn
    have ha2 : 2 ≤ a := Nat.succ_le_of_lt (lt_of_le_of_ne ha (Ne.symm hn))
    have hl : 31867*2+47468*1 ≤ 31867*a+47468*b :=
      Nat.add_le_add (Nat.mul_le_mul_left _ ha2) (Nat.mul_le_mul_left _ hb)
    rw [← he,hp] at hl
    norm_num at hl
  · by_contra hn
    have hb2 : 2 ≤ b := Nat.succ_le_of_lt (lt_of_le_of_ne hb (Ne.symm hn))
    have hl : 31867*1+47468*2 ≤ 31867*a+47468*b :=
      Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hb2)
    rw [← he,hp] at hl
    norm_num at hl


private theorem image_coprime (t : ℕ) :
    syracuseStep t % 2 = 1 ∧ ¬ 3 ∣ syracuseStep t := by
  have hne : 3*t+1 ≠ 0 := by omega
  have hnot2 : ¬ 2 ∣ syracuseStep t := Nat.not_dvd_ordCompl Nat.prime_two hne
  refine ⟨by omega,?_⟩
  intro h3
  have hd := dvd_trans h3 (Nat.ordCompl_dvd (3*t+1) 2)
  omega

private theorem one_mod_four_descent (t : ℕ) (ht : 1 < t) (hr : t%4 = 1) :
    syracuseStep t < t := by
  have hl : 2 ∣ 3*t+1 := by omega
  have hr' : 2 ∣ (3*t+1)/2 := by omega
  have hd : syracuseStep t = ordCompl[2] ((3*t+1)/4) := by
    rw [syracuseStep, ← Nat.ordCompl_div_of_dvd Nat.prime_two hl,
      ← Nat.ordCompl_div_of_dvd Nat.prime_two hr',
      show (3*t+1)/2/2=(3*t+1)/4 by omega]
  rw [hd]
  exact (Nat.div_le_self _ _).trans_lt (by omega)

private theorem period_minimum_residue (m p B U : ℕ) (hp : 0 < p) (hB : 1 < B)
    (hcycle : syracuseStep^[p] m = m)
    (hFloor : ∀ i : ℕ, B ≤ syracuseStep^[i] m)
    (hVisit : ∃ i : ℕ, syracuseStep^[i] m < U) :
    ∃ j < p, B ≤ syracuseStep^[j] m ∧ syracuseStep^[j] m < U ∧
      (syracuseStep^[j] m % 12 = 7 ∨ syracuseStep^[j] m % 12 = 11) ∧
      ∀ i : ℕ, syracuseStep^[j] m ≤ syracuseStep^[i] m := by
  let V := Set.range (fun i : ℕ => syracuseStep^[i] m)
  let x := sInf V
  obtain ⟨i,hi⟩ := (Nat.sInf_mem (Set.range_nonempty _) : x ∈ V)
  let j := i%p
  have hc : Function.IsPeriodicPt syracuseStep p m := hcycle
  have hj : syracuseStep^[j] m = x := (hc.iterate_mod_apply i).trans hi
  have hMin (i : ℕ) : x ≤ syracuseStep^[i] m := Nat.sInf_le ⟨i,rfl⟩
  obtain ⟨k,hk⟩ := hVisit
  refine ⟨j,Nat.mod_lt _ hp,hFloor j,?_,?_,?_⟩
  · exact hj.trans_lt ((hMin k).trans_lt hk)
  · have hjreturn : syracuseStep^[p] (syracuseStep^[j] m) = syracuseStep^[j] m := by
      rw [← Function.iterate_add_apply, Nat.add_comm p j, Function.iterate_add_apply, hcycle]
    obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [hl, Function.iterate_succ_apply'] at hjreturn
    have ⟨ho,h3⟩ := image_coprime (syracuseStep^[l] (syracuseStep^[j] m))
    rw [hjreturn] at ho h3
    have ht : 1 < syracuseStep^[j] m := hB.trans_le (hFloor j)
    have hnot1 : syracuseStep^[j] m % 4 ≠ 1 := by
      intro h1
      have hd := one_mod_four_descent (syracuseStep^[j] m) ht h1
      have hd' : syracuseStep^[j+1] m < syracuseStep^[j] m :=
        (Function.iterate_succ_apply' syracuseStep j m).trans_lt hd
      exact (Nat.not_lt_of_ge (hj.trans_le (hMin (j+1)))) hd'
    omega
  · intro i'
    exact hj.trans_le (hMin i')

private theorem nontrivial_period_floor (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    ∀ i : ℕ, 1241513984 ≤ syracuseStep^[i] m := by
  intro i
  by_contra hsmall
  have hpos : 0 < syracuseStep^[i] m := by
    cases i with
    | zero => exact hm
    | succ j =>
      rw [Function.iterate_succ_apply']
      exact Nat.ordCompl_pos 2 (by omega)
  have hreturn : syracuseStep^[p] (syracuseStep^[i] m) = syracuseStep^[i] m := by
    rw [← Function.iterate_add_apply, Nat.add_comm p i, Function.iterate_add_apply,hcyc]
  have hone := syracuse_no_cycle_below_1241513984 _ p hpos hp (Nat.lt_of_not_ge hsmall) hreturn
  exact hne (syracuse_periodic_reaches_one _ _ hp hcyc ⟨i,hone⟩)


private theorem sum_periodic_shift (f : ℕ → ℝ) (p s : ℕ)
    (hPeriod : ∀ i, f (i+p) = f i) :
    (∑ i ∈ Finset.range p, f (i+s)) = ∑ i ∈ Finset.range p, f i := by
  induction s with
  | zero => simp
  | succ s ih =>
    have he (i : ℕ) : i+1+s=i+(s+1) := by omega
    have hEnd : f (p+s) = f s := by rw [Nat.add_comm p s,hPeriod]
    have hs1 := Finset.sum_range_succ (fun i => f (i+s)) p
    have hs2 := Finset.sum_range_succ' (fun i => f (i+s)) p
    simp only [hEnd] at hs1
    simp only [he,Nat.zero_add] at hs2
    calc
      _ = ∑ i ∈ Finset.range p, f (i+s) := by linarith only [hs1,hs2]
      _ = _ := ih

private theorem cycle_harmonic_five (m p B : ℕ) (hp : 0 < p) (hB : 2000 ≤ B)
    (hcycle : syracuseStep^[p] m = m) (hfloor : ∀ i : ℕ, B ≤ syracuseStep^[i] m) :
    (∑ i ∈ Finset.range p, (1:ℝ)/(syracuseStep^[i] m:ℝ)) ≤ (p:ℝ)*79/(100*(B:ℝ)) := by
  let x (i : ℕ) := syracuseStep^[i] m
  let e (i : ℕ) := (3*x i+1).factorization 2
  let w (i : ℕ) : ℝ := 1/(x i:ℝ)
  have hXp (i : ℕ) : x (i+p) = x i := by
    change syracuseStep^[i+p] m = syracuseStep^[i] m
    rw [Function.iterate_add_apply,hcycle]
  have hodd (i : ℕ) : x i % 2 = 1 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [← hXp i,hk,show i+(k+1) = (i+k)+1 by omega]
    change syracuseStep^[(i+k)+1] m % 2 = 1
    rw [Function.iterate_succ_apply']
    exact (image_coprime _).1
  have hStep (i : ℕ) : 2^(e i)*x (i+1) = 3*x i+1 := by
    have he : x (i+1) = syracuseStep (x i) := Function.iterate_succ_apply' _ _ _
    rw [he]
    exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hEp (i : ℕ) : 0 < e i := by
    by_contra h
    have he : e i = 0 := by omega
    have hf := hStep i
    rw [he,pow_zero,one_mul] at hf
    have ha := hodd i
    have hb := hodd (i+1)
    omega
  have hFive (i : ℕ) : (∑ j ∈ Finset.range 5, w (i+j)) ≤ 79/(20*(B:ℝ)) :=
    five_row_reciprocal_budget B (fun j => x (i+j)) (fun j => e (i+j)) hB
      (fun j _ => hfloor (i+j)) (fun j _ => hEp (i+j))
      (fun j _ => by simpa only [Nat.add_assoc] using hStep (i+j))
  have hwp (i : ℕ) : w (i+p) = w i := by simp only [w,hXp]
  have he :
      (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range 5, w (i+j)) =
        5 * (∑ i ∈ Finset.range p, w i) := by
    rw [Finset.sum_comm]
    simp [sum_periodic_shift w p _ hwp]
  have hs : 5*(∑ i ∈ Finset.range p, w i) ≤ (p:ℝ)*(79/(20*(B:ℝ))) := calc
    _ = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range 5, w (i+j) := he.symm
    _ ≤ ∑ i ∈ Finset.range p, 79/(20*(B:ℝ)) := Finset.sum_le_sum (fun i _ => hFive i)
    _ = _ := by simp
  have hu : (p:ℝ)*(79/(20*(B:ℝ))) = 5*((p:ℝ)*79/(100*(B:ℝ))) := by ring
  rw [hu] at hs
  exact le_of_mul_le_mul_left hs (by norm_num)

private theorem period_five_log_upper (m p B : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hB : 2000 ≤ B) (hcycle : syracuseStep^[p] m = m)
    (hfloor : ∀ i : ℕ, B ≤ syracuseStep^[i] m) :
    let K := (Finset.range p).sum fun i => (3*syracuseStep^[i] m+1).factorization 2
    (K:ℝ)*Real.log 2 ≤ (p:ℝ)*(Real.log 3+79/(300*(B:ℝ))) := by
  intro K
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  let H := ∑ i ∈ Finset.range p, (1:ℝ)/(syracuseStep^[i] m:ℝ)
  have hH : H ≤ (p:ℝ)*79/(100*(B:ℝ)) := cycle_harmonic_five m p B hp hB hcycle hfloor
  have hpowers : (2:ℝ)^K ≤ (3:ℝ)^p*Real.exp (H/3) := by
    apply le_of_mul_le_mul_right _ hmr
    have h := product_le_exp_reciprocal_sum m p hm
    rw [hcycle] at h
    calc
      _ ≤ (3:ℝ)^p*(m:ℝ)*Real.exp (H/3) := h
      _ = _ := by ring
  have hlog := Real.log_le_log (by positivity) hpowers
  rw [Real.log_mul (by positivity : (3:ℝ)^p ≠ 0) (Real.exp_ne_zero _),
    Real.log_pow,Real.log_pow,Real.log_exp] at hlog
  calc
    _ ≤ (p:ℝ)*Real.log 3 + H/3 := hlog
    _ ≤ (p:ℝ)*Real.log 3 + ((p:ℝ)*79/(100*(B:ℝ)))/3 := by
      have hv : H/3 ≤ ((p:ℝ)*79/(100*(B:ℝ)))/3 :=
        div_le_div_of_nonneg_right hH (by norm_num)
      linarith only [hv]
    _ = _ := by ring

private theorem upper_visit (m p : ℕ) (hm : 0 < m) (hp : p = 79335)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    ∃ i, syracuseStep^[i] m < 5710000000 := by
  have hpPos : 0 < p := by omega
  let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
  have hK : K = 125743 := by
    obtain ⟨_,a,b,ha,hb,hPeriod,hValue⟩ :=
      syracuse_nontrivial_period_coordinates_at_1241513984 m p hm hpPos hcycle hne
    obtain ⟨ha1,hb1⟩ := first_coordinate_unique p a b hp ha hb hPeriod
    change K = _ at hValue
    rw [hValue,ha1,hb1]
  by_contra hNo
  have hB (i : ℕ) : 5710000000 ≤ syracuseStep^[i] m :=
    Nat.le_of_not_gt (fun h => hNo ⟨i,h⟩)
  have hh : (K:ℝ)*Real.log 2 ≤ (p:ℝ)*(Real.log 3+79/(300*5710000000)) :=
    period_five_log_upper m p 5710000000 hm hpPos (by decide) hcycle hB
  rw [hK,hp] at hh
  obtain ⟨h2l,_,_,h3u⟩ := log_bounds
  have hUp : (79335:ℝ)*(Real.log 3+79/(300*5710000000)) < 125743*Real.log 2 := calc
    _ ≤ (79335:ℝ)*(u3+79/(300*5710000000)) :=
      mul_le_mul_of_nonneg_left (add_le_add h3u.le le_rfl) (by norm_num)
    _ < 125743*l2 := by norm_num [u3,l2]
    _ ≤ _ := mul_le_mul_of_nonneg_left h2l.le (by norm_num)
  exact (not_lt_of_ge hh) hUp

/-- The candidate period 79,335 forces a minimum in a narrower interval. -/
theorem solution (m : ℕ) (hm : 0 < m)
    (hcycle : syracuseStep^[79335] m = m) (hne : m ≠ 1) :
    ∃ j < 79335, 1241513984 ≤ syracuseStep^[j] m ∧ syracuseStep^[j] m < 5710000000 ∧
      (syracuseStep^[j] m % 12 = 7 ∨ syracuseStep^[j] m % 12 = 11) ∧
      ∀ i : ℕ, syracuseStep^[j] m ≤ syracuseStep^[i] m := by
  have hFloor := nontrivial_period_floor m 79335 hm (by decide) hcycle hne
  exact period_minimum_residue m 79335 1241513984 5710000000 (by decide) (by decide)
    hcycle hFloor (upper_visit m 79335 hm rfl hcycle hne)
