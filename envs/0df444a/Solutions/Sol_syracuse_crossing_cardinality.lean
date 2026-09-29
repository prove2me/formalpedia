-- Prove2me | solution 1 for syracuse_crossing_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T05:32:58.069908+00:00
-- url     : https://prove2.me/submissions/3691d611-1652-4242-8296-e02de14271bc

/-
  Standalone producer for the actual Syracuse crossing-input count.

  The public conclusion is only the deterministic finite cardinality estimate.
  The published crossing-residue count and valuation-prefix residue-forcing
  interfaces are reused; the Syracuse orbit-label adapters are local.
-/

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_crossing_residue_cardinality
import Theorems.Thm_syracuse_valuation_prefix_residue

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

private def crossingExponent (N i : ℕ) : ℕ :=
  (3 * (syracuseStep^[i]) N + 1).factorization 2

private lemma step_input_pos (n : ℕ) (hn : 0 < n) : 0 < 3 * n + 1 := by omega

private lemma step_pos {n : ℕ} (hn : 0 < n) : 0 < syracuseStep n := by
  apply Nat.ordCompl_pos
  exact (step_input_pos n hn).ne'

private lemma step_odd {n : ℕ} (hn : 0 < n) : Odd (syracuseStep n) := by
  have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
    Nat.coprime_ordCompl Nat.prime_two (step_input_pos n hn).ne'
  exact hcop.odd_of_left

private lemma two_dvd_step_input {n : ℕ} (hodd : Odd n) : 2 ∣ 3 * n + 1 := by
  obtain ⟨k, hk⟩ := hodd
  rw [hk]
  exact ⟨3 * k + 2, by omega⟩

private lemma exponent_pos {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < (3 * n + 1).factorization 2 := by
  apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two
  · exact (step_input_pos n hn).ne'
  · exact two_dvd_step_input hodd

private lemma step_chain (n : ℕ) :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  simpa [syracuseStep] using Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

private lemma iterate_pos_odd (N : ℕ) (hN : 0 < N) (hodd : Odd N) (i : ℕ) :
    0 < (syracuseStep^[i]) N ∧ Odd ((syracuseStep^[i]) N) := by
  induction i with
  | zero => simpa using And.intro hN hodd
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨step_pos ih.1, step_odd ih.1⟩

private lemma iterate_exponent_pos (N i : ℕ) (hN : 0 < N) (hodd : Odd N) :
    0 < crossingExponent N i := by
  unfold crossingExponent
  obtain ⟨hi, ho⟩ := iterate_pos_odd N hN hodd i
  exact exponent_pos hi ho

private lemma iterate_chain (N i : ℕ) :
    2 ^ crossingExponent N i * (syracuseStep^[i + 1]) N =
      3 * (syracuseStep^[i]) N + 1 := by
  simpa [crossingExponent, Function.iterate_succ_apply'] using
    step_chain ((syracuseStep^[i]) N)

private theorem exists_first_crossing (a : ℕ → ℕ) :
    ∀ (t q : ℕ), 0 < q → q ≤ ∑ i ∈ Finset.range t, a i →
      ∃ k < t,
        (∑ i ∈ Finset.range k, a i) < q ∧
          q ≤ (∑ i ∈ Finset.range k, a i) + a k
  | 0, q, hq, hsum => by
      simp at hsum
      omega
  | t + 1, q, hq, hsum => by
      by_cases hp : q ≤ ∑ i ∈ Finset.range t, a i
      · obtain ⟨k, hkt, hlt, hcross⟩ := exists_first_crossing a t q hq hp
        exact ⟨k, lt_trans hkt (Nat.lt_succ_self t), hlt, hcross⟩
      · have hlt : (∑ i ∈ Finset.range t, a i) < q := Nat.lt_of_not_ge hp
        exact ⟨t, Nat.lt_succ_self t, hlt, by simpa [Finset.sum_range_succ] using hsum⟩

private theorem crossing_pow_dvd
    (q k : ℕ) (a : ℕ → ℕ) (next current : ℕ)
    (hcross : q ≤ (∑ i ∈ Finset.range k, a i) + a k)
    (hchain : 2 ^ a k * next = 3 * current + 1) :
    2 ^ (q - ∑ i ∈ Finset.range k, a i) ∣ 3 * current + 1 := by
  have hle : q - (∑ i ∈ Finset.range k, a i) ≤ a k := by omega
  exact (pow_dvd_pow 2 hle).trans ⟨next, hchain.symm⟩

private abbrev PrefixLabel (t q : ℕ) :=
  Σ k : Fin t, {a : Fin k → Fin q //
    (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < q}

private def crossingIndex
    (N t q : ℕ) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, crossingExponent N i) : ℕ :=
  Classical.choose (exists_first_crossing (fun i => crossingExponent N i) t q hq hsum)

private lemma crossingIndex_spec
    (N t q : ℕ) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, crossingExponent N i) :
    crossingIndex N t q hq hsum < t ∧
      (∑ i ∈ Finset.range (crossingIndex N t q hq hsum), crossingExponent N i) < q ∧
      q ≤ (∑ i ∈ Finset.range (crossingIndex N t q hq hsum), crossingExponent N i) +
        crossingExponent N (crossingIndex N t q hq hsum) := by
  exact Classical.choose_spec
    (exists_first_crossing (fun i => crossingExponent N i) t q hq hsum)

private lemma exponent_le_prefix (N k : ℕ) (i : Fin k) :
    crossingExponent N i.val ≤ ∑ j ∈ Finset.range k, crossingExponent N j := by
  apply Finset.single_le_sum
  · intro j hj
    exact Nat.zero_le _
  · exact Finset.mem_range.mpr i.isLt

private def crossingLabel
    (N t q : ℕ) (hN : 0 < N) (hodd : Odd N) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, crossingExponent N i) : PrefixLabel t q := by
  let k := crossingIndex N t q hq hsum
  have hk : k < t := (crossingIndex_spec N t q hq hsum).1
  refine ⟨⟨k, hk⟩, ?_⟩
  refine ⟨(fun i => ⟨crossingExponent N i.val, ?_⟩), ?_, ?_⟩
  · exact lt_of_le_of_lt (exponent_le_prefix N k i) (crossingIndex_spec N t q hq hsum).2.1
  · intro i
    exact iterate_exponent_pos N i.val hN hodd
  · rw [Fin.sum_univ_eq_sum_range]
    simpa using (crossingIndex_spec N t q hq hsum).2.1

private lemma crossingLabel_fst
    (N t q : ℕ) (hN : 0 < N) (hodd : Odd N) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, crossingExponent N i) :
    (crossingLabel N t q hN hodd hq hsum).1.1 = crossingIndex N t q hq hsum := by
  rfl

private lemma crossingLabel_value
    (N t q : ℕ) (hN : 0 < N) (hodd : Odd N) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, crossingExponent N i)
    (i : Fin (crossingIndex N t q hq hsum)) :
    (crossingLabel N t q hN hodd hq hsum).2.1 i =
      ⟨crossingExponent N i.val,
        lt_of_le_of_lt (exponent_le_prefix N (crossingIndex N t q hq hsum) i)
          (crossingIndex_spec N t q hq hsum).2.1⟩ := by
  rfl

private def labelAt {t q : ℕ} (i : Fin t) (L : PrefixLabel t q) : ℕ :=
  if hi : i.val < L.1.val then (L.2.1 ⟨i.val, hi⟩).val else 0

private theorem equal_labels_modEq
    (N₁ N₂ t q : ℕ) (hN₁ : 0 < N₁) (ho₁ : Odd N₁)
    (hN₂ : 0 < N₂) (ho₂ : Odd N₂) (hq : 0 < q)
    (hs₁ : q ≤ ∑ i ∈ Finset.range t, crossingExponent N₁ i)
    (hs₂ : q ≤ ∑ i ∈ Finset.range t, crossingExponent N₂ i)
    (heq : crossingLabel N₁ t q hN₁ ho₁ hq hs₁ =
      crossingLabel N₂ t q hN₂ ho₂ hq hs₂) :
    Nat.ModEq (2 ^ q) N₁ N₂ := by
  let L₁ := crossingLabel N₁ t q hN₁ ho₁ hq hs₁
  let L₂ := crossingLabel N₂ t q hN₂ ho₂ hq hs₂
  change L₁ = L₂ at heq
  have hindex : L₁.1.val = L₂.1.val := congrArg (fun L : PrefixLabel t q => L.1.val) heq
  have hindex_raw : crossingIndex N₁ t q hq hs₁ = crossingIndex N₂ t q hq hs₂ := by
    calc
      crossingIndex N₁ t q hq hs₁ = L₁.1.val := by
        symm
        simpa [L₁] using crossingLabel_fst N₁ t q hN₁ ho₁ hq hs₁
      _ = L₂.1.val := hindex
      _ = crossingIndex N₂ t q hq hs₂ := by
        simpa [L₂] using crossingLabel_fst N₂ t q hN₂ ho₂ hq hs₂
  let k := crossingIndex N₁ t q hq hs₁
  have hval_eq (i : Fin k) : crossingExponent N₁ i.val = crossingExponent N₂ i.val := by
    have hk : k < t := (crossingIndex_spec N₁ t q hq hs₁).1
    let j : Fin t := ⟨i.val, lt_trans i.isLt hk⟩
    have hj : labelAt j L₁ = labelAt j L₂ :=
      congrArg (fun L : PrefixLabel t q => labelAt j L) heq
    have hi₂ : i.val < crossingIndex N₂ t q hq hs₂ := by
      rw [← hindex_raw]
      exact i.isLt
    have hkL₁ : L₁.1.val = k := by
      simpa [L₁, k] using crossingLabel_fst N₁ t q hN₁ ho₁ hq hs₁
    have hkL₂ : L₂.1.val = crossingIndex N₂ t q hq hs₂ := by
      simpa [L₂] using crossingLabel_fst N₂ t q hN₂ ho₂ hq hs₂
    have hv₁ := crossingLabel_value N₁ t q hN₁ ho₁ hq hs₁ i
    have hv₂ := crossingLabel_value N₂ t q hN₂ ho₂ hq hs₂ ⟨i.val, hi₂⟩
    have hji₁ : j.val < L₁.1.val := by rw [hkL₁]; exact i.isLt
    have hji₂ : j.val < L₂.1.val := by rw [hkL₂]; exact hi₂
    have hij₁ : (⟨j.val, hji₁⟩ : Fin L₁.1.val) = i := by
      apply Fin.ext
      rfl
    have hij₂ : (⟨j.val, hji₂⟩ : Fin L₂.1.val) = ⟨i.val, hi₂⟩ := by
      apply Fin.ext
      rfl
    have hleft : labelAt j L₁ = crossingExponent N₁ i.val := by
      simp only [labelAt, dif_pos hji₁]
      rw [hij₁]
      simpa [L₁] using congrArg (fun v : Fin q => v.val) hv₁
    have hright : labelAt j L₂ = crossingExponent N₂ i.val := by
      simp only [labelAt, dif_pos hji₂]
      rw [hij₂]
      exact congrArg (fun v : Fin q => v.val) hv₂
    exact hleft.symm.trans (hj.trans hright)
  have hsum_eq :
      (∑ i ∈ Finset.range k, crossingExponent N₁ i) =
        ∑ i ∈ Finset.range k, crossingExponent N₂ i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hval_eq ⟨i, Finset.mem_range.mp hi⟩
  have hrec₁ : ∀ i, i < k →
      2 ^ crossingExponent N₁ i * (syracuseStep^[i + 1]) N₁ =
        3 * (syracuseStep^[i]) N₁ + 1 := by
    intro i hi
    exact iterate_chain N₁ i
  have hrec₂ : ∀ i, i < k →
      2 ^ crossingExponent N₁ i * (syracuseStep^[i + 1]) N₂ =
        3 * (syracuseStep^[i]) N₂ + 1 := by
    intro i hi
    rw [hval_eq ⟨i, hi⟩]
    exact iterate_chain N₂ i
  have hs₁' := crossingIndex_spec N₁ t q hq hs₁
  have hs₂' := crossingIndex_spec N₂ t q hq hs₂
  have hf₁ : 2 ^ (q - ∑ i ∈ Finset.range k, crossingExponent N₁ i) ∣
      3 * (syracuseStep^[k]) N₁ + 1 := by
    apply crossing_pow_dvd q k (fun i => crossingExponent N₁ i)
      ((syracuseStep^[k + 1]) N₁) ((syracuseStep^[k]) N₁)
    · simpa [k] using hs₁'.2.2
    · exact iterate_chain N₁ k
  have hf₂ : 2 ^ (q - ∑ i ∈ Finset.range k, crossingExponent N₁ i) ∣
      3 * (syracuseStep^[k]) N₂ + 1 := by
    rw [hsum_eq]
    apply crossing_pow_dvd q k (fun i => crossingExponent N₂ i)
      ((syracuseStep^[k + 1]) N₂) ((syracuseStep^[k]) N₂)
    · simpa [k, hindex_raw] using hs₂'.2.2
    · exact iterate_chain N₂ k
  exact syracuse_valuation_prefix_residue k q (fun i => crossingExponent N₁ i)
    (fun i => (syracuseStep^[i]) N₁) (fun i => (syracuseStep^[i]) N₂) hrec₁ hrec₂
    (by simpa [k] using hs₁'.2.1) hf₁ hf₂

theorem solution (b q t : ℕ) (hq : 0 < q) (hqb : q ≤ b) :
    (Finset.univ.filter (fun x : Fin (2 ^ b) =>
      0 < x.val ∧ Odd x.val ∧
        q ≤ ∑ i ∈ Finset.range t,
          (3 * (syracuseStep^[i]) x.val + 1).factorization 2)).card ≤
      2 ^ (b - q) * (∑ k : Fin t, Nat.choose (q - 1) k) := by
  let S := Finset.univ.filter (fun x : Fin (2 ^ b) =>
    0 < x.val ∧ Odd x.val ∧ q ≤ ∑ i ∈ Finset.range t, crossingExponent x.val i)
  let label : {x // x ∈ S} → PrefixLabel t q := fun x =>
    crossingLabel x.1.1 t q
      (by
        have hx := x.2
        simp [S] at hx
        exact hx.1)
      (by
        have hx := x.2
        simp [S] at hx
        exact hx.2.1)
      hq
      (by
        have hx := x.2
        simp [S] at hx
        exact hx.2.2)
  have hlabel : ∀ x y, label x = label y → Nat.ModEq (2 ^ q) x.1.1 y.1.1 := by
    intro x y hxy
    have hx := x.2
    have hy := y.2
    simp [S] at hx hy
    apply equal_labels_modEq x.1.1 y.1.1 t q hx.1 hx.2.1 hy.1 hy.2.1 hq hx.2.2 hy.2.2
    simpa [label] using hxy
  have hcard := crossing_residue_cardinality b q t hq hqb S label hlabel
  simpa [S, crossingExponent] using hcard

#print axioms solution
