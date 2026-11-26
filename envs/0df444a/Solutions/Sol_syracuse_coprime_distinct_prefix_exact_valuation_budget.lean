-- Prove2me | solution 1 for syracuse_coprime_distinct_prefix_exact_valuation_budget
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:46:46.020855+00:00
-- url     : https://prove2.me/submissions/4e868ed1-575e-430e-9af8-9110347f5976

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/- The sorted-product comparison is adapted from FormallyCorrect's accepted
   Prove2Me solution 8c188af5-f0ae-4343-b8c0-4a1447008e8b (Apache-2.0).
   This version retains the endpoint of an arbitrary prefix and uses the
   separation of numbers coprime to six. -/

private def rankOffset (i : ℕ) : ℕ := 6 * (i / 2) + 2 * (i % 2)

private theorem coprime_finset_rank_lower (s : Finset ℕ) (B : ℕ)
    (hodd : ∀ x ∈ s, x % 2 = 1) (hthree : ∀ x ∈ s, ¬ 3 ∣ x)
    (hB : ∀ x ∈ s, B ≤ x) :
    ∀ j (hj : j < s.card), B + rankOffset j ≤ s.orderEmbOfFin rfl ⟨j,hj⟩ := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    cases j with
    | zero => simpa [rankOffset] using hB _ (s.orderEmbOfFin_mem rfl ⟨0,hj⟩)
    | succ j =>
      cases j with
      | zero =>
        have hz : 0 < s.card := by omega
        let a := s.orderEmbOfFin rfl ⟨0,hz⟩
        let b := s.orderEmbOfFin rfl ⟨1,hj⟩
        have hab : a < b := (s.orderEmbOfFin rfl).strictMono (by exact Nat.zero_lt_one)
        have ha : a ∈ s := s.orderEmbOfFin_mem rfl ⟨0,hz⟩
        have hb : b ∈ s := s.orderEmbOfFin_mem rfl ⟨1,hj⟩
        have hfa := hB a ha
        have hoa := hodd a ha
        have hob := hodd b hb
        change B+2 ≤ b
        omega
      | succ j =>
        have h0 : j < s.card := by omega
        have h1 : j+1 < s.card := by omega
        let a := s.orderEmbOfFin rfl ⟨j,h0⟩
        let b := s.orderEmbOfFin rfl ⟨j+1,h1⟩
        let c := s.orderEmbOfFin rfl ⟨j+2,hj⟩
        have hab : a < b := (s.orderEmbOfFin rfl).strictMono (by exact Nat.lt_succ_self j)
        have hbc : b < c := (s.orderEmbOfFin rfl).strictMono (by exact Nat.lt_succ_self (j+1))
        have ha : a ∈ s := s.orderEmbOfFin_mem rfl ⟨j,h0⟩
        have hb : b ∈ s := s.orderEmbOfFin_mem rfl ⟨j+1,h1⟩
        have hc : c ∈ s := s.orderEmbOfFin_mem rfl ⟨j+2,hj⟩
        have hoa := hodd a ha
        have hob := hodd b hb
        have hoc := hodd c hc
        have hta := hthree a ha
        have htb := hthree b hb
        have htc := hthree c hc
        have hbnd : B + rankOffset j ≤ a := ih j (by omega) h0
        have hsep : a + 6 ≤ c := by
          by_contra hn
          have hbe : b = a+2 := by omega
          have hce : c = a+4 := by omega
          have hcases : a%3 = 1 ∨ a%3 = 2 := by omega
          rcases hcases with h | h
          · exact htb (by omega)
          · exact htc (by omega)
        change B+rankOffset (j+2) ≤ c
        unfold rankOffset at hbnd ⊢
        omega

private theorem coprime_finset_ratio_product_bound (s : Finset ℕ) (B : ℕ) (hBpos : 0 < B)
    (hodd : ∀ x ∈ s, x % 2 = 1) (hthree : ∀ x ∈ s, ¬ 3 ∣ x)
    (hB : ∀ x ∈ s, B ≤ x) :
    (∏ x ∈ s, (3 * (x : ℚ) + 1) / x) ≤
      ∏ i ∈ Finset.range s.card, (3 * ((B + rankOffset i : ℕ) : ℚ) + 1) /
        ((B + rankOffset i : ℕ) : ℚ) := by
  classical
  conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rw [Finset.prod_range]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    have hbound := coprime_finset_rank_lower s B hodd hthree hB i.val i.isLt
    have hxpos : (0 : ℚ) < s.orderEmbOfFin rfl i := by
      exact_mod_cast (lt_of_lt_of_le hBpos (hB _ (s.orderEmbOfFin_mem rfl i)))
    have hbpos : (0 : ℚ) < (B + rankOffset i.val : ℕ) := by positivity
    have hcast : ((B + rankOffset i.val : ℕ) : ℚ) ≤ s.orderEmbOfFin rfl i := by
      exact_mod_cast hbound
    apply (div_le_div_iff₀ hxpos hbpos).2
    change (3 * (s.orderEmbOfFin rfl i : ℚ) + 1) * ((B + rankOffset i.val : ℕ) : ℚ) ≤
      (3 * ((B + rankOffset i.val : ℕ) : ℚ) + 1) * (s.orderEmbOfFin rfl i : ℚ)
    nlinarith

private theorem stepProperties (x : ℕ) : 0 < syracuseStep x ∧
    syracuseStep x % 2 = 1 ∧ ¬ 3 ∣ syracuseStep x := by
  have hne : 3*x+1 ≠ 0 := by omega
  have he : ¬ 2 ∣ syracuseStep x := Nat.not_dvd_ordCompl Nat.prime_two hne
  refine ⟨Nat.ordCompl_pos 2 hne, by omega, ?_⟩
  intro hd
  have h := dvd_trans hd (Nat.ordCompl_dvd (3*x+1) 2)
  omega

private theorem ratioIdentity (n k : ℕ) (hn : 0 < n) :
    (∏ i ∈ Finset.range k, (3 * (syracuseStep^[i] n : ℚ) + 1) / syracuseStep^[i] n) =
      (2 : ℚ)^((Finset.range k).sum fun i => (3 * syracuseStep^[i] n+1).factorization 2) *
        (syracuseStep^[k] n : ℚ) / n := by
  let x (j : ℕ) := syracuseStep^[j] n
  let A (j : ℕ) := (Finset.range j).sum fun i => (3*x i+1).factorization 2
  show (∏ i ∈ Finset.range k, (3*(x i : ℚ)+1)/x i) = (2:ℚ)^(A k)*x k/n
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  induction k with
  | zero => simp [x,A,hnq]
  | succ k ih =>
    have hpos : 0 < x k := by
      cases k with
      | zero => exact hn
      | succ j =>
        change 0 < syracuseStep^[j+1] n
        rw [Function.iterate_succ_apply']
        exact (stepProperties _).1
    let a := (3*x k+1).factorization 2
    have hA : A (k+1) = A k + a := Finset.sum_range_succ _ _
    have hrow : 2^a*x (k+1) = 3*x k+1 := by
      have hx : x (k+1) = syracuseStep (x k) := Function.iterate_succ_apply' _ _ _
      rw [hx]
      exact Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcast : (2:ℚ)^a*(x (k+1) : ℚ) = 3*(x k : ℚ)+1 := by exact_mod_cast hrow
    have hxq : (x k : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Finset.prod_range_succ, ih, hA, pow_add, ← hcast]
    field_simp [hnq,hxq]

/-- Exact finite-product bound on a nonrepeating Syracuse segment of states coprime to six. -/
theorem solution (n B k : ℕ)
    (hB : 0 < B) (hodd : n % 2 = 1) (hthree : ¬ 3 ∣ n)
    (hfloor : ∀ i < k, B ≤ syracuseStep^[i] n)
    (hinj : Set.InjOn (fun i : ℕ => syracuseStep^[i] n) {i | i < k}) :
    2^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
        syracuseStep^[k] n * (∏ i ∈ Finset.range k, (B+6*(i/2)+2*(i%2))) ≤
      n * (∏ i ∈ Finset.range k, (3*(B+6*(i/2)+2*(i%2))+1)) := by
  let x (i : ℕ) := syracuseStep^[i] n
  have hInject : Set.InjOn x (↑(Finset.range k) : Set ℕ) := by
    intro i hi j hj h
    exact hinj (by simpa using hi) (by simpa using hj) h
  let s := (Finset.range k).image x
  have hc : s.card = k := (Finset.card_image_of_injOn hInject).trans (Finset.card_range k)
  have hmem (y : ℕ) (hy : y ∈ s) : ∃ i < k, x i = y := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  have hprops (i : ℕ) : x i % 2 = 1 ∧ ¬ 3 ∣ x i := by
    cases i with
    | zero => exact ⟨hodd,hthree⟩
    | succ i =>
      change syracuseStep^[i+1] n % 2 = 1 ∧ ¬ 3 ∣ syracuseStep^[i+1] n
      rw [Function.iterate_succ_apply']
      exact (stepProperties _).2
  have hbound := coprime_finset_ratio_product_bound s B hB
    (fun y hy => by obtain ⟨i,_,rfl⟩ := hmem y hy; exact (hprops i).1)
    (fun y hy => by obtain ⟨i,_,rfl⟩ := hmem y hy; exact (hprops i).2)
    (fun y hy => by obtain ⟨i,hi,rfl⟩ := hmem y hy; exact hfloor i hi)
  have hn : 0 < n := by omega
  rw [hc, Finset.prod_image hInject, ratioIdentity n k hn, Finset.prod_div_distrib] at hbound
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hden : (0 : ℚ) < ∏ i ∈ Finset.range k, ((B+rankOffset i : ℕ) : ℚ) := by
    apply Finset.prod_pos
    intro i _
    positivity
  have hm := (div_le_div_iff₀ hnq hden).mp hbound
  simp only [rankOffset, ← Nat.add_assoc] at hm
  rw [mul_comm _ (n : ℚ)] at hm
  exact_mod_cast (show _ ≤ _ from hm)
