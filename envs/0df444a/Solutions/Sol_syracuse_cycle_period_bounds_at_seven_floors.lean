-- Prove2me | solution 1 for syracuse_cycle_period_bounds_at_seven_floors
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:28:02.780302+00:00
-- url     : https://prove2.me/submissions/7e217383-b028-41a0-b644-265dcdd2c65d

import Mathlib
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three

open scoped BigOperators

private abbrev l2 : ℝ := 0.693147180559945309417232121458176568075500134359
private abbrev u2 : ℝ := 0.693147180559945309417232121458176568075500134362
private abbrev l3 : ℝ := 1.098612288668109691395245236922525704647490557820
private abbrev u3 : ℝ := 1.098612288668109691395245236922525704647490557825

set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
private theorem log_bounds :
    l2 < Real.log 2 ∧ Real.log 2 < u2 ∧ l3 < Real.log 3 ∧ Real.log 3 < u3 := by
  have ha := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/3) (by norm_num) 100
  have hb := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/4) (by norm_num) 100
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

private theorem period_log_band (m p B : ℕ) (hp : 0 < p) (hB : 0 < B)
    (hf : ∀ i : ℕ, B ≤ syracuseStep^[i] m) (hcyc : syracuseStep^[p] m = m) :
    let K := (Finset.range p).sum fun i => (3*syracuseStep^[i] m+1).factorization 2
    (p:ℝ)*Real.log 3 < (K:ℝ)*Real.log 2 ∧
      (K:ℝ)*Real.log 2 ≤ (p:ℝ)*(Real.log 3 + 1/(3*(B:ℝ))) := by
  intro K
  have hm : 0 < m := hB.trans_le (hf 0)
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hfine : (3:ℝ)^p < (2:ℝ)^K := by
    exact_mod_cast (show 3^p < 2^K from syracuse_cycle_pow_two_gt_pow_three m p hm hp hcyc)
  have hlogfine := Real.log_lt_log (by positivity) hfine
  rw [Real.log_pow,Real.log_pow] at hlogfine
  refine ⟨hlogfine,?_⟩
  let H := ∑ i ∈ Finset.range p, (1:ℝ)/(syracuseStep^[i] m:ℝ)
  have hH : H ≤ (p:ℝ)/(B:ℝ) := calc
    _ ≤ ∑ i ∈ Finset.range p, (1:ℝ)/(B:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply one_div_le_one_div_of_le hBr
      exact_mod_cast hf i
    _ = _ := by simp [div_eq_mul_inv]
  have hpowers : (2:ℝ)^K ≤ (3:ℝ)^p*Real.exp (H/3) := by
    apply le_of_mul_le_mul_right _ hmr
    have h := product_le_exp_reciprocal_sum m p hm
    rw [hcyc] at h
    calc
      _ ≤ (3:ℝ)^p*(m:ℝ)*Real.exp (H/3) := h
      _ = _ := by ring
  have hlog := Real.log_le_log (by positivity) hpowers
  rw [Real.log_mul (by positivity : (3:ℝ)^p ≠ 0) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_pow, Real.log_exp] at hlog
  calc
    _ ≤ (p:ℝ)*Real.log 3 + H/3 := hlog
    _ ≤ (p:ℝ)*Real.log 3 + ((p:ℝ)/(B:ℝ))/3 := by
      have hv : H/3 ≤ ((p:ℝ)/(B:ℝ))/3 :=
        div_le_div_of_nonneg_right hH (by norm_num)
      linarith only [hv]
    _ = _ := by ring

private theorem integer_lower_edge (p K lp lk : ℕ) (hp : 0 < p)
    (hlo : (p:ℝ)*Real.log 3 < (K:ℝ)*Real.log 2)
    (hl : (lk:ℝ)*Real.log 2 < (lp:ℝ)*Real.log 3) :
    lk*p < lp*K := by
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : (lk:ℝ)*p*Real.log 2 < (lp:ℝ)*K*Real.log 2 := calc
    _ = (p:ℝ)*((lk:ℝ)*Real.log 2) := by ring
    _ < (p:ℝ)*((lp:ℝ)*Real.log 3) := mul_lt_mul_of_pos_left hl hpr
    _ = (lp:ℝ)*((p:ℝ)*Real.log 3) := by ring
    _ ≤ (lp:ℝ)*((K:ℝ)*Real.log 2) := mul_le_mul_of_nonneg_left hlo.le (by positivity)
    _ = _ := by ring
  exact_mod_cast (lt_of_mul_lt_mul_right hb hpos.le)

private theorem integer_upper_edge (p K B up uk : ℕ) (hp : 0 < p)
    (hhi : (K:ℝ)*Real.log 2 ≤ (p:ℝ)*(Real.log 3+1/(3*(B:ℝ))))
    (hu : (up:ℝ)*(Real.log 3+1/(3*(B:ℝ))) < (uk:ℝ)*Real.log 2) :
    up*K < uk*p := by
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : (up:ℝ)*K*Real.log 2 < (uk:ℝ)*p*Real.log 2 := calc
    _ = (up:ℝ)*((K:ℝ)*Real.log 2) := by ring
    _ ≤ (up:ℝ)*((p:ℝ)*(Real.log 3+1/(3*(B:ℝ)))) :=
      mul_le_mul_of_nonneg_left hhi (by positivity)
    _ = (p:ℝ)*((up:ℝ)*(Real.log 3+1/(3*(B:ℝ)))) := by ring
    _ < (p:ℝ)*((uk:ℝ)*Real.log 2) := mul_lt_mul_of_pos_left hu hpr
    _ = _ := by ring
  exact_mod_cast (lt_of_mul_lt_mul_right hb hpos.le)

private theorem farey_denominator_bound (p K lp lk up uk : ℕ)
    (hdet : uk*lp = lk*up+1) (hl : lk*p < lp*K) (hu : up*K < uk*p) :
    lp+up ≤ p := by
  let a : ℤ := (uk:ℤ)*p-(up:ℤ)*K
  let b : ℤ := (lp:ℤ)*K-(lk:ℤ)*p
  have hdetz : (uk:ℤ)*lp = (lk:ℤ)*up+1 := by exact_mod_cast hdet
  have hdz : (uk:ℤ)*lp-(lk:ℤ)*up=1 := by linarith only [hdetz]
  have ha : 1 ≤ a := by
    have z : (up:ℤ)*K < (uk:ℤ)*p := by exact_mod_cast hu
    dsimp [a]
    omega
  have hb : 1 ≤ b := by
    have z : (lk:ℤ)*p < (lp:ℤ)*K := by exact_mod_cast hl
    dsimp [b]
    omega
  have hsum : (lp:ℤ)*a+(up:ℤ)*b = p := calc
    _ = ((uk:ℤ)*lp-(lk:ℤ)*up)*(p:ℤ) := by dsimp [a,b]; ring
    _ = _ := by rw [hdz,one_mul]
  have hla : (lp:ℤ) ≤ (lp:ℤ)*a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha (by positivity : (0:ℤ) ≤ lp)
  have hub : (up:ℤ) ≤ (up:ℤ)*b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (by positivity : (0:ℤ) ≤ up)
  exact_mod_cast (show (lp:ℤ)+up ≤ p by linarith only [hsum,hla,hub])

/-- Strict lower edge and certified period bounds at seven orbit floors. -/
theorem solution (m p B : ℕ) (hp : 0 < p) (hB : 0 < B)
    (hf : ∀ i : ℕ, B ≤ syracuseStep^[i] m) (hcyc : syracuseStep^[p] m = m) :
    let K := (Finset.range p).sum fun i => (3*syracuseStep^[i] m+1).factorization 2
    16785921*p < 10590737*K ∧
    (8000000000 ≤ B → 190537 ≤ p) ∧
    (1000000000000 ≤ B → 10781274 ≤ p) ∧
    (1000000000000000 ≤ B → 64497107 ≤ p) ∧
    (1000000000000000000 ≤ B → 397573379 ≤ p) ∧
    (1000000000000000000000000 ≤ B → 2396860564955 ≤ p) ∧
    (1000000000000000000000000000000 ≤ B → 2849242656677982 ≤ p) ∧
    (340282366920938463463374607431768211456 ≤ B → 27444133206411171953 ≤ p) := by
  intro K
  obtain ⟨h2l,h2u,h3l,h3u⟩ := log_bounds
  have hLower (lp lk : ℕ) (h : (lk:ℝ)*u2 < (lp:ℝ)*l3) :
      (lk:ℝ)*Real.log 2 < (lp:ℝ)*Real.log 3 :=
    (mul_le_mul_of_nonneg_left h2u.le (by positivity)).trans_lt
      (h.trans_le (mul_le_mul_of_nonneg_left h3l.le (by positivity)))
  have hUpper (F up uk : ℕ) (h : (up:ℝ)*(u3+1/(3*(F:ℝ))) < (uk:ℝ)*l2) :
      (up:ℝ)*(Real.log 3+1/(3*(F:ℝ))) < (uk:ℝ)*Real.log 2 := by
    have hmid : Real.log 3+1/(3*(F:ℝ)) ≤ u3+1/(3*(F:ℝ)) := add_le_add h3u.le le_rfl
    calc
      _ ≤ (up:ℝ)*(u3+1/(3*(F:ℝ))) := mul_le_mul_of_nonneg_left hmid (by positivity)
      _ < (uk:ℝ)*l2 := h
      _ ≤ _ := mul_le_mul_of_nonneg_left h2l.le (by positivity)
  have first (F lp lk up uk : ℕ) (hF : 0 < F) (hFB : F ≤ B) (hd : uk*lp = lk*up+1)
      (hl : (lk:ℝ)*u2 < (lp:ℝ)*l3)
      (hu : (up:ℝ)*(u3+1/(3*(F:ℝ))) < (uk:ℝ)*l2) :
      lp+up ≤ p := by
    obtain ⟨ha,hb⟩ := period_log_band m p F hp hF (fun i => hFB.trans (hf i)) hcyc
    exact farey_denominator_bound p K lp lk up uk hd
      (integer_lower_edge p K lp lk hp ha (hLower _ _ hl))
      (integer_upper_edge p K F up uk hp hb (hUpper _ _ _ hu))
  refine ⟨integer_lower_edge p K 10590737 16785921 hp (period_log_band m p B hp hB hf hcyc).1
      (hLower _ _ (by norm_num [u2,l3])), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb
    exact first 8000000000 111202 176251 79335 125743
      (by decide) hb (by decide) (by norm_num [u2,l3]) (by norm_num [u3,l2])
  · intro hb
    exact first 1000000000000 10590737 16785921 190537 301994
      (by decide) hb (by decide) (by norm_num [u2,l3]) (by norm_num [u3,l2])
  · intro hb
    exact first 1000000000000000 53715833 85137581 10781274 17087915
      (by decide) hb (by decide) (by norm_num [u2,l3]) (by norm_num [u3,l2])
  · intro hb
    exact first 1000000000000000000 225644606 357638239 171928773 272500658
      (by decide) hb (by decide) (by norm_num [u2,l3]) (by norm_num [u3,l2])
  · intro hb
    exact first 1000000000000000000000000 753110839881 1193652440098 1643749725074 2605281674813
      (by decide) hb (by decide) (by norm_num [u2,l3]) (by norm_num [u3,l2])
  · intro hb
    exact first 1000000000000000000000000000000 483615324366283 766512153894657 2365627332311699 3749430612395068
      (by decide) hb (by decide) (by norm_num [u2,l3]) (by norm_num [u3,l2])
  · intro hb
    exact first 340282366920938463463374607431768211456 22803850947114245497 36143248623210700400 4640282259296926456 7354673373747273033
      (by decide) hb (by decide) (by norm_num [u2,l3]) (by norm_num [u3,l2])
