-- Prove2me | solution 1 for syracuse_first_passage_fixed_target_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T11:06:04.273067+00:00
-- url     : https://prove2.me/submissions/97eaa9f1-9472-48a7-a2e0-34dc0608a84d

import Mathlib
import Definitions.Def_syracuseStep

open scoped BigOperators

private def valve (n : ℕ) : ℕ := (3*n+1).factorization 2

private def halfValve (n : ℕ) : ℕ := (valve n-1)/2

private theorem row (n : ℕ) : 2^(valve n)*syracuseStep n = 3*n+1 :=
  Nat.ordProj_mul_ordCompl_eq_self _ _

private theorem imageOdd (n : ℕ) : syracuseStep n % 2 = 1 := by
  have h : ¬ 2 ∣ syracuseStep n := Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3*n+1 ≠ 0)
  omega

private theorem valve_pos (n : ℕ) (hn : n%2=1) : 0 < valve n :=
  Nat.prime_two.factorization_pos_of_dvd (by omega) (by omega)

private theorem step_and_halfValve_injective {x y : ℕ} (hx : x%2=1) (hy : y%2=1)
    (hstep : syracuseStep x = syracuseStep y) (hq : halfValve x = halfValve y) : x = y := by
  have hxp := valve_pos x hx
  have hyp := valve_pos y hy
  have hrowx := row x
  have hrowy := row y
  unfold halfValve at hq
  have hcases : valve x = valve y ∨ valve x = valve y+1 ∨ valve y = valve x+1 := by omega
  rcases hcases with h|h|h
  · rw [h,hstep,hrowy] at hrowx
    omega
  · rw [h,pow_succ',mul_assoc,hstep,hrowy] at hrowx
    omega
  · rw [h,pow_succ',mul_assoc,← hstep,hrowx] at hrowy
    omega

private theorem iterOdd (n : ℕ) (hn : n%2=1) (i : ℕ) : syracuseStep^[i] n % 2 = 1 := by
  cases i with
  | zero => exact hn
  | succ j => rw [Function.iterate_succ_apply']; exact imageOdd _

private theorem halfValve_word_injective (x y k : ℕ) (ho : x%2=1) (ho' : y%2=1)
    (hEnd : syracuseStep^[k] x = syracuseStep^[k] y)
    (hword : ∀ i < k, halfValve (syracuseStep^[i] x) = halfValve (syracuseStep^[i] y)) : x = y := by
  have hback (j : ℕ) (hj : j ≤ k) : syracuseStep^[k-j] x = syracuseStep^[k-j] y := by
    induction j with
    | zero => simpa using hEnd
    | succ j ih =>
      have hprev := ih (by omega)
      have hind : (k-(j+1)).succ = k-j := by omega
      apply step_and_halfValve_injective (iterOdd x ho _) (iterOdd y ho' _)
      · rw [← Function.iterate_succ_apply' syracuseStep (k-(j+1)) x,
            ← Function.iterate_succ_apply' syracuseStep (k-(j+1)) y, hind,hprev]
      · exact hword (k-(j+1)) (by omega)
  simpa using hback k (Nat.le_refl _)

private theorem sum_halfValve_budget (n k B X a M : ℕ) (ho : n%2=1) (_hB : 0 < B)
    (hX : n ≤ X) (hF : ∀ i < k, B ≤ syracuseStep^[i] n)
    (hEnd : syracuseStep^[k] n = a)
    (hCut : X*(3*B+1)^k < 2^(2*(M+1)+k)*a*B^k) :
    (∑ i ∈ Finset.range k, halfValve (syracuseStep^[i] n)) ≤ M := by
  let x (j : ℕ) := syracuseStep^[j] n
  let A (j : ℕ) := ∑ i ∈ Finset.range j, valve (x i)
  let Q (j : ℕ) := ∑ i ∈ Finset.range j, halfValve (x i)
  have hQ (j : ℕ) : 2*Q j+j ≤ A j := by
    induction j with
    | zero => simp [Q,A]
    | succ j ih =>
      have hpos := valve_pos _ (iterOdd n ho j)
      change 0 < valve (x j) at hpos
      have he : 2*halfValve (x j)+1 ≤ valve (x j) := by unfold halfValve; omega
      change 2*(∑ i ∈ Finset.range (j+1), halfValve (x i))+(j+1) ≤
        ∑ i ∈ Finset.range (j+1), valve (x i)
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      change 2*(Q j+halfValve (x j))+(j+1) ≤ A j+valve (x j)
      omega
  have hA (j : ℕ) (hj : j ≤ k) : 2^(A j)*x j*B^j ≤ n*(3*B+1)^j := by
    induction j with
    | zero => simp [A,x]
    | succ j ih =>
      have hj' : j < k := by omega
      have hf : B ≤ x j := hF j hj'
      have hrow : 2^(valve (x j))*x (j+1) = 3*x j+1 := by
        rw [show x (j+1) = syracuseStep (x j) from Function.iterate_succ_apply' _ _ _]
        exact row _
      have hinn : B*(3*x j+1) ≤ (3*B+1)*x j := by nlinarith
      have hAsucc : A (j+1) = A j+valve (x j) := Finset.sum_range_succ _ _
      calc
        _ = (2^(A j)*B^j)*(B*(2^(valve (x j))*x (j+1))) := by
          rw [hAsucc,pow_add,pow_succ]; ac_rfl
        _ = (2^(A j)*B^j)*(B*(3*x j+1)) := by rw [hrow]
        _ ≤ (2^(A j)*B^j)*((3*B+1)*x j) := Nat.mul_le_mul_left _ hinn
        _ = (3*B+1)*(2^(A j)*x j*B^j) := by ac_rfl
        _ ≤ (3*B+1)*(n*(3*B+1)^j) := Nat.mul_le_mul_left _ (ih (by omega))
        _ = n*(3*B+1)^(j+1) := by rw [pow_succ]; ac_rfl
  change Q k ≤ M
  by_contra hh
  have he : 2*(M+1)+k ≤ A k := by have := hQ k; omega
  have hp := Nat.pow_le_pow_right (by decide : 0<2) he
  have hX' := Nat.mul_le_mul_right ((3*B+1)^k) hX
  have hProd := hA k (Nat.le_refl _)
  change x k = a at hEnd
  rw [hEnd] at hProd
  exact (Nat.not_le_of_gt hCut)
    ((Nat.mul_le_mul_right (B^k) (Nat.mul_le_mul_right a hp)).trans (hProd.trans hX'))

private theorem word_finset_card {α : Type*} (S : Finset α) (k M : ℕ)
    (code : α → ℕ → ℕ)
    (hsum : ∀ x ∈ S, (∑ j ∈ Finset.range k, code x j) ≤ M)
    (hcode : ∀ x ∈ S, ∀ y ∈ S, (∀ j < k, code x j = code y j) → x = y) :
    S.card ≤ (M+k).choose k := by
  classical
  let Q (x : α) (t : ℕ) := ∑ j ∈ Finset.range t, code x j
  let p (x : α) (j : ℕ) := j + Q x (j+1)
  have hQ (x : α) (j : ℕ) : Q x (j+1) = Q x j + code x j := Finset.sum_range_succ _ _
  have hp (x : α) : StrictMono (p x) := by
    apply strictMono_nat_of_lt_succ
    intro j
    change j + Q x (j+1) < j+1 + Q x (j+2)
    rw [hQ x (j+1)]
    omega
  let F (x : α) : Finset ℕ := Finset.univ.image (fun j : Fin k => p x j)
  have hF_card (x : α) : (F x).card = k := by
    change (Finset.univ.image (fun j : Fin k => p x j)).card = k
    have hi : Function.Injective (fun j : Fin k => p x j) := fun _ _ h =>
      Fin.val_injective ((hp x).injective h)
    rw [Finset.card_image_of_injective _ hi,
        Finset.card_univ, Fintype.card_fin]
  have hF_range (x : α) : (F x : Set ℕ) = Set.range (fun j : Fin k => p x j) := by simp [F]
  rw [← Finset.card_range (M+k), ← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn F
  · intro x hx
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hF_card x⟩
    intro v hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    have hj : j.val + 1 ≤ k := j.isLt
    have hle : Q x (j.val+1) ≤ Q x k := Finset.sum_le_sum_of_subset
      (Finset.range_mono hj)
    have hM : Q x k ≤ M := hsum x hx
    apply Finset.mem_range.mpr
    change j.val + Q x (j.val+1) < M+k
    omega
  · intro x hx y hy hxy
    have heq : Set.range (fun j : Fin k => p x j) = Set.range (fun j : Fin k => p y j) := by
      rw [← hF_range, ← hF_range, hxy]
    have hfun := (StrictMono.range_inj ((hp x).comp Fin.val_strictMono)
      ((hp y).comp Fin.val_strictMono)).mp heq
    have hpoint (j : ℕ) (hj : j < k) : p x j = p y j := congrFun hfun ⟨j,hj⟩
    apply hcode x hx y hy
    intro j hj
    have hcur := hpoint j hj
    change j+Q x (j+1) = j+Q y (j+1) at hcur
    rw [hQ,hQ] at hcur
    cases j with
    | zero => simpa [Q] using hcur
    | succ j =>
      have hprev := hpoint j (by omega)
      change j+Q x (j+1) = j+Q y (j+1) at hprev
      omega

private theorem last_halfValve_pos {n a B : ℕ} (hBefore : 2*B ≤ n)
    (hEnd : syracuseStep n = a) (hUpper : 2*a+2 ≤ 3*B) :
    1 ≤ halfValve n := by
  unfold halfValve
  by_contra hh
  have hv : valve n ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hv
  have hle := Nat.mul_le_mul_right a hp
  have hr := row n
  rw [hEnd] at hr
  rw [hr] at hle
  norm_num at hle
  omega

theorem solution (S : Finset ℕ) (B X a d M : ℕ)
    (hB : 0 < B) (hUpper : 2*a+2 ≤ 3*B)
    (hCut : X*(6*B+1)^(d+1) < 2^(2*(M+1)+(d+1))*a*(2*B)^(d+1))
    (hS : ∀ n ∈ S, n ≤ X ∧ n%2 = 1 ∧ syracuseStep^[d+1] n = a ∧
      ∀ i ≤ d, 2*B ≤ syracuseStep^[i] n) :
    S.card ≤ (M+d).choose (d+1) := by
  classical
  by_cases hm : M = 0
  · have hEmpty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hx,ho,hEnd,hF⟩ := hS n hn
      have hQ := sum_halfValve_budget n (d+1) (2*B) X a M ho (by omega) hx
        (fun i hi => hF i (by omega)) hEnd (by simpa [show 3*(2*B)+1 = 6*B+1 by ring] using hCut)
      rw [Finset.sum_range_succ] at hQ
      have hLast := last_halfValve_pos (hF d (Nat.le_refl _))
        ((Function.iterate_succ_apply' _ _ _).symm.trans hEnd) hUpper
      omega
    simp [hEmpty]
  have hs (n : ℕ) (hn : n ∈ S) :
      1 ≤ halfValve (syracuseStep^[d] n) ∧
      (∑ i ∈ Finset.range (d+1), halfValve (syracuseStep^[i] n)) ≤ M := by
    obtain ⟨hx,ho,hEnd,hF⟩ := hS n hn
    exact ⟨last_halfValve_pos (hF d (Nat.le_refl _))
        ((Function.iterate_succ_apply' _ _ _).symm.trans hEnd) hUpper,
      sum_halfValve_budget n (d+1) (2*B) X a M ho (by omega) hx
        (fun i hi => hF i (by omega)) hEnd (by simpa [show 3*(2*B)+1 = 6*B+1 by ring] using hCut)⟩
  let q (n i : ℕ) := halfValve (syracuseStep^[i] n) - (if i = d then 1 else 0)
  have hQ (n : ℕ) (hn : n ∈ S) :
      (∑ i ∈ Finset.range (d+1), q n i) ≤ M-1 := by
    obtain ⟨hLast,hSum⟩ := hs n hn
    rw [Finset.sum_range_succ] at hSum ⊢
    have heq : (∑ i ∈ Finset.range d, q n i) =
        ∑ i ∈ Finset.range d, halfValve (syracuseStep^[i] n) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simp [q, show i ≠ d by omega]
    rw [heq,show q n d = halfValve (syracuseStep^[d] n) - 1 by simp [q]]
    omega
  have hInject (n : ℕ) (hn : n ∈ S) (m : ℕ) (hm' : m ∈ S)
      (hc : ∀ i < d+1, q n i = q m i) : n = m := by
    obtain ⟨_,ho,hEnd,_⟩ := hS n hn
    obtain ⟨_,ho',hEnd',_⟩ := hS m hm'
    apply halfValve_word_injective n m (d+1) ho ho' (hEnd.trans hEnd'.symm)
    intro i hi
    have h := hc i hi
    by_cases he : i = d
    · subst i
      have hn' := (hs n hn).1
      have hm'' := (hs m hm').1
      simp [q] at h
      omega
    · simpa [q,he] using h
  have out := word_finset_card S (d+1) (M-1) q hQ hInject
  rwa [show M-1+(d+1)=M+d by omega] at out
