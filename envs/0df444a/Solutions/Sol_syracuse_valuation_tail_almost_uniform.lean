-- Prove2me | solution 1 for syracuse_valuation_tail_almost_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T06:33:53.332481+00:00
-- url     : https://prove2.me/submissions/73618a7b-aef1-4cc4-8728-3b9952dd784c

/-
  Standalone source-faithful finite-L¹ consumer for Tao's Lemma 4.1 shape.
  The finite residue approximation is explicit; this is not Proposition 1.9
  or Theorem 3.1 itself.
-/

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_positive_exponent_prefix_cardinality
import Theorems.Thm_syracuse_valuation_prefix_residue
import Theorems.Thm_binomial_prefix_tail_of_linear_gap

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators
open Classical

noncomputable section

def platformSyracuseExponent (N i : ℕ) : ℕ :=
  (3 * (syracuseStep^[i]) N + 1).factorization 2

private lemma platform_two_dvd_three_mul_add_one_of_odd {n : ℕ} (hn : Odd n) :
    2 ∣ 3 * n + 1 := by
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  refine ⟨3 * k + 2, ?_⟩
  omega

lemma platform_syracuse_step_pos {n : ℕ} (hn : 0 < n) : 0 < syracuseStep n := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.ordCompl_pos
  exact hpos.ne'

lemma platform_syracuse_step_odd {n : ℕ} (hn : 0 < n) : Odd (syracuseStep n) := by
  have hpos : 0 < 3 * n + 1 := by omega
  have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
    Nat.coprime_ordCompl Nat.prime_two hpos.ne'
  exact hcop.odd_of_left

lemma platform_syracuse_step_factorization_pos {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) :
    0 < (3 * n + 1).factorization 2 := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two
  · exact hpos.ne'
  · exact platform_two_dvd_three_mul_add_one_of_odd hodd

lemma platform_syracuse_step_factorization_mul {n : ℕ} :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  simpa [syracuseStep] using Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

lemma platform_syracuse_iterate_pos_odd (N : ℕ) (hN : 0 < N) (hodd : Odd N) (i : ℕ) :
    0 < (syracuseStep^[i]) N ∧ Odd ((syracuseStep^[i]) N) := by
  induction i with
  | zero => simpa using And.intro hN hodd
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨platform_syracuse_step_pos ih.1, platform_syracuse_step_odd ih.1⟩

lemma platform_syracuse_exponent_pos (N i : ℕ) (hN : 0 < N) (hodd : Odd N) :
    0 < platformSyracuseExponent N i := by
  unfold platformSyracuseExponent
  obtain ⟨hi_pos, hi_odd⟩ := platform_syracuse_iterate_pos_odd N hN hodd i
  exact platform_syracuse_step_factorization_pos hi_pos hi_odd

lemma platform_syracuse_exponent_chain (N i : ℕ) :
    2 ^ platformSyracuseExponent N i * (syracuseStep^[i + 1]) N =
      3 * (syracuseStep^[i]) N + 1 := by
  simpa [platformSyracuseExponent, Function.iterate_succ_apply'] using
    (platform_syracuse_step_factorization_mul (n := (syracuseStep^[i]) N))

lemma platform_exists_first_crossing (a : ℕ → ℕ) :
    ∀ (t q : ℕ), 0 < q → q ≤ ∑ i ∈ Finset.range t, a i →
      ∃ k < t,
        (∑ i ∈ Finset.range k, a i) < q ∧
          q ≤ (∑ i ∈ Finset.range k, a i) + a k
  | 0, q, hq, hsum => by simp at hsum; omega
  | t + 1, q, hq, hsum => by
      by_cases hprefix : q ≤ ∑ i ∈ Finset.range t, a i
      · obtain ⟨k, hkt, hlt, hcross⟩ :=
          platform_exists_first_crossing a t q hq hprefix
        exact ⟨k, lt_trans hkt (Nat.lt_succ_self t), hlt, hcross⟩
      · have hlt : (∑ i ∈ Finset.range t, a i) < q := Nat.lt_of_not_ge hprefix
        refine ⟨t, Nat.lt_succ_self t, hlt, ?_⟩
        simpa [Finset.sum_range_succ] using hsum

def platformPositivePrefixLabel (n n' : ℕ) :=
  Σ k : Fin n, {a : Fin k → Fin n' //
    (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'}

instance platformPositivePrefixLabelFintype (n n' : ℕ) :
    Fintype (platformPositivePrefixLabel n n') := by
  unfold platformPositivePrefixLabel
  infer_instance

lemma platform_card_positivePrefixLabel (n n' : ℕ) (hn' : 0 < n') :
    Fintype.card (platformPositivePrefixLabel n n') =
      ∑ k : Fin n, Nat.choose (n' - 1) k := by
  simp only [platformPositivePrefixLabel, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  exact positive_exponent_prefix_cardinality k n' hn'

def platformSyracuseResidue (N q : ℕ) (_hq : 0 < q) : Fin (2 ^ q) :=
  ⟨N % 2 ^ q, Nat.mod_lt _ (by positivity)⟩

def platformSyracuseCrossingIndex
    (N t q : ℕ) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i) : ℕ :=
  Classical.choose
    (platform_exists_first_crossing (fun i => platformSyracuseExponent N i) t q hq hsum)

lemma platformSyracuseCrossingIndex_spec
    (N t q : ℕ) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i) :
    platformSyracuseCrossingIndex N t q hq hsum < t ∧
      (∑ i ∈ Finset.range (platformSyracuseCrossingIndex N t q hq hsum),
        platformSyracuseExponent N i) < q ∧
      q ≤ (∑ i ∈ Finset.range (platformSyracuseCrossingIndex N t q hq hsum),
        platformSyracuseExponent N i) +
        platformSyracuseExponent N (platformSyracuseCrossingIndex N t q hq hsum) := by
  exact Classical.choose_spec
    (platform_exists_first_crossing (fun i => platformSyracuseExponent N i) t q hq hsum)

private lemma platform_exponent_le_prefix
    (N k : ℕ) (i : Fin k) :
    platformSyracuseExponent N i.val ≤
      ∑ j ∈ Finset.range k, platformSyracuseExponent N j := by
  apply Finset.single_le_sum
  · intro j hj; exact Nat.zero_le _
  · exact Finset.mem_range.mpr i.isLt

def platformPositivePrefixLabelOfCrossing
    (N t q : ℕ) (hN : 0 < N) (hodd : Odd N) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i) :
    platformPositivePrefixLabel t q := by
  let k := platformSyracuseCrossingIndex N t q hq hsum
  have hk : k < t := (platformSyracuseCrossingIndex_spec N t q hq hsum).1
  refine ⟨⟨k, hk⟩, ?_⟩
  refine ⟨(fun i => ⟨platformSyracuseExponent N i.val, ?_⟩), ?_, ?_⟩
  · exact lt_of_le_of_lt (platform_exponent_le_prefix N k i)
      (platformSyracuseCrossingIndex_spec N t q hq hsum).2.1
  · intro i
    exact platform_syracuse_exponent_pos N i.val hN hodd
  · rw [Fin.sum_univ_eq_sum_range]
    simpa using (platformSyracuseCrossingIndex_spec N t q hq hsum).2.1

lemma platform_label_fst
    (N t q : ℕ) (hN : 0 < N) (hodd : Odd N) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i) :
    (platformPositivePrefixLabelOfCrossing N t q hN hodd hq hsum).1.1 =
      platformSyracuseCrossingIndex N t q hq hsum := by rfl

lemma platform_label_value
    (N t q : ℕ) (hN : 0 < N) (hodd : Odd N) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i)
    (i : Fin (platformSyracuseCrossingIndex N t q hq hsum)) :
    (platformPositivePrefixLabelOfCrossing N t q hN hodd hq hsum).2.1 i =
      ⟨platformSyracuseExponent N i.val,
        lt_of_le_of_lt (platform_exponent_le_prefix
          N (platformSyracuseCrossingIndex N t q hq hsum) i)
          (platformSyracuseCrossingIndex_spec N t q hq hsum).2.1⟩ := by rfl

private def platformPositivePrefixLabelAt {t q : ℕ}
    (i : Fin t) (L : platformPositivePrefixLabel t q) : ℕ :=
  if hi : i.val < L.1.val then (L.2.1 ⟨i.val, hi⟩).val else 0

private lemma platform_crossing_pow_dvd
    (q k : ℕ) (a : ℕ → ℕ) (next current : ℕ)
    (hcross : q ≤ (∑ i ∈ Finset.range k, a i) + a k)
    (hchain : 2 ^ a k * next = 3 * current + 1) :
    2 ^ (q - ∑ i ∈ Finset.range k, a i) ∣ 3 * current + 1 := by
  have hle : q - (∑ i ∈ Finset.range k, a i) ≤ a k := by omega
  exact (pow_dvd_pow 2 hle).trans ⟨next, hchain.symm⟩

theorem platform_equal_crossing_labels_modEq
    (N₁ N₂ t q : ℕ) (hN₁ : 0 < N₁) (hodd₁ : Odd N₁)
    (hN₂ : 0 < N₂) (hodd₂ : Odd N₂) (hq : 0 < q)
    (hsum₁ : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N₁ i)
    (hsum₂ : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N₂ i)
    (heq : platformPositivePrefixLabelOfCrossing N₁ t q hN₁ hodd₁ hq hsum₁ =
      platformPositivePrefixLabelOfCrossing N₂ t q hN₂ hodd₂ hq hsum₂) :
    Nat.ModEq (2 ^ q) N₁ N₂ := by
  let L₁ := platformPositivePrefixLabelOfCrossing N₁ t q hN₁ hodd₁ hq hsum₁
  let L₂ := platformPositivePrefixLabelOfCrossing N₂ t q hN₂ hodd₂ hq hsum₂
  change L₁ = L₂ at heq
  have hindex : L₁.1.val = L₂.1.val := congrArg (fun L => L.1.val) heq
  have hindex_raw : platformSyracuseCrossingIndex N₁ t q hq hsum₁ =
      platformSyracuseCrossingIndex N₂ t q hq hsum₂ := by
    calc
      platformSyracuseCrossingIndex N₁ t q hq hsum₁ = L₁.1.val := by
        symm
        simpa [L₁] using platform_label_fst N₁ t q hN₁ hodd₁ hq hsum₁
      _ = L₂.1.val := hindex
      _ = platformSyracuseCrossingIndex N₂ t q hq hsum₂ := by
        simpa [L₂] using platform_label_fst N₂ t q hN₂ hodd₂ hq hsum₂
  let k := platformSyracuseCrossingIndex N₁ t q hq hsum₁
  have hval_eq (i : Fin k) :
      platformSyracuseExponent N₁ i.val = platformSyracuseExponent N₂ i.val := by
    have hk : k < t := by
      exact (platformSyracuseCrossingIndex_spec N₁ t q hq hsum₁).1
    let j : Fin t := ⟨i.val, lt_trans i.isLt hk⟩
    have hj : platformPositivePrefixLabelAt j L₁ =
        platformPositivePrefixLabelAt j L₂ :=
      congrArg (fun L => platformPositivePrefixLabelAt j L) heq
    have hi₂ : i.val < platformSyracuseCrossingIndex N₂ t q hq hsum₂ := by
      rw [← hindex_raw]
      exact i.isLt
    have hkL₁ : L₁.1.val = k := by
      simpa [L₁, k] using platform_label_fst N₁ t q hN₁ hodd₁ hq hsum₁
    have hkL₂ : L₂.1.val = platformSyracuseCrossingIndex N₂ t q hq hsum₂ := by
      simpa [L₂] using platform_label_fst N₂ t q hN₂ hodd₂ hq hsum₂
    have hv₁ := platform_label_value N₁ t q hN₁ hodd₁ hq hsum₁ i
    have hv₂ := platform_label_value N₂ t q hN₂ hodd₂ hq hsum₂ ⟨i.val, hi₂⟩
    have hji₁ : j.val < L₁.1.val := by rw [hkL₁]; exact i.isLt
    have hji₂ : j.val < L₂.1.val := by rw [hkL₂]; exact hi₂
    have hij₁ : (⟨j.val, hji₁⟩ : Fin L₁.1.val) = i := by
      apply Fin.ext
      rfl
    have hij₂ : (⟨j.val, hji₂⟩ : Fin L₂.1.val) = ⟨i.val, hi₂⟩ := by
      apply Fin.ext
      rfl
    have hleft : platformPositivePrefixLabelAt j L₁ =
        platformSyracuseExponent N₁ i.val := by
      simp only [platformPositivePrefixLabelAt, dif_pos hji₁]
      rw [hij₁]
      simpa [L₁] using congrArg (fun v : Fin q => v.val) hv₁
    have hright : platformPositivePrefixLabelAt j L₂ =
        platformSyracuseExponent N₂ i.val := by
      simp only [platformPositivePrefixLabelAt, dif_pos hji₂]
      rw [hij₂]
      exact congrArg (fun v : Fin q => v.val) hv₂
    exact hleft.symm.trans (hj.trans hright)
  have hsum_eq :
      (∑ i ∈ Finset.range k, platformSyracuseExponent N₁ i) =
        ∑ i ∈ Finset.range k, platformSyracuseExponent N₂ i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hval_eq ⟨i, Finset.mem_range.mp hi⟩
  have hrec₁ : ∀ i, i < k →
      2 ^ platformSyracuseExponent N₁ i * (syracuseStep^[i + 1]) N₁ =
        3 * (syracuseStep^[i]) N₁ + 1 := by
    intro i hi
    exact platform_syracuse_exponent_chain N₁ i
  have hrec₂ : ∀ i, i < k →
      2 ^ platformSyracuseExponent N₁ i * (syracuseStep^[i + 1]) N₂ =
        3 * (syracuseStep^[i]) N₂ + 1 := by
    intro i hi
    rw [hval_eq ⟨i, hi⟩]
    exact platform_syracuse_exponent_chain N₂ i
  have hspec₁ := platformSyracuseCrossingIndex_spec N₁ t q hq hsum₁
  have hspec₂ := platformSyracuseCrossingIndex_spec N₂ t q hq hsum₂
  have hfinal₁ :
      2 ^ (q - ∑ i ∈ Finset.range k, platformSyracuseExponent N₁ i) ∣
        3 * (syracuseStep^[k]) N₁ + 1 := by
    apply platform_crossing_pow_dvd q k (fun i => platformSyracuseExponent N₁ i)
      ((syracuseStep^[k + 1]) N₁) ((syracuseStep^[k]) N₁)
    · simpa [k] using hspec₁.2.2
    · exact platform_syracuse_exponent_chain N₁ k
  have hfinal₂ :
      2 ^ (q - ∑ i ∈ Finset.range k, platformSyracuseExponent N₁ i) ∣
        3 * (syracuseStep^[k]) N₂ + 1 := by
    rw [hsum_eq]
    apply platform_crossing_pow_dvd q k (fun i => platformSyracuseExponent N₂ i)
      ((syracuseStep^[k + 1]) N₂) ((syracuseStep^[k]) N₂)
    · simpa [k, hindex_raw] using hspec₂.2.2
    · exact platform_syracuse_exponent_chain N₂ k
  apply syracuse_valuation_prefix_residue k q
    (fun i => platformSyracuseExponent N₁ i)
    (fun i => (syracuseStep^[i]) N₁) (fun i => (syracuseStep^[i]) N₂) hrec₁ hrec₂
  · simpa [k] using hspec₁.2.1
  · exact hfinal₁
  · exact hfinal₂

def platformPositivePrefixLabelRealized
    (t q : ℕ) (hq : 0 < q) (L : platformPositivePrefixLabel t q) (N : ℕ) : Prop :=
  ∃ hN : 0 < N, ∃ hodd : Odd N,
    ∃ hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i,
      platformPositivePrefixLabelOfCrossing N t q hN hodd hq hsum = L

def platformSyracuseResidueForLabel
    (t q : ℕ) (hq : 0 < q) (L : platformPositivePrefixLabel t q) : Fin (2 ^ q) := by
  classical
  exact if h : ∃ N, platformPositivePrefixLabelRealized t q hq L N then
    platformSyracuseResidue (Classical.choose h) q hq else ⟨0, by positivity⟩

lemma platformSyracuseResidueForLabel_eq_of_realized
    (t q : ℕ) (hq : 0 < q) (L : platformPositivePrefixLabel t q) (N : ℕ)
    (hreal : platformPositivePrefixLabelRealized t q hq L N) :
    platformSyracuseResidueForLabel t q hq L = platformSyracuseResidue N q hq := by
  classical
  unfold platformSyracuseResidueForLabel
  split_ifs with hex
  · let N₀ := Classical.choose hex
    have h₀ := Classical.choose_spec hex
    have hN₀ : 0 < N₀ := h₀.choose
    have h₁ := h₀.choose_spec
    have hodd₀ : Odd N₀ := h₁.choose
    have h₂ := h₁.choose_spec
    have hsum₀ : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N₀ i := h₂.choose
    have hL₀ := h₂.choose_spec
    have hN : 0 < N := hreal.choose
    have h₃ := hreal.choose_spec
    have hodd : Odd N := h₃.choose
    have h₄ := h₃.choose_spec
    have hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i := h₄.choose
    have hL := h₄.choose_spec
    have hmod : Nat.ModEq (2 ^ q) N₀ N :=
      platform_equal_crossing_labels_modEq N₀ N t q hN₀ hodd₀ hN hodd hq
        hsum₀ hsum (hL₀.trans hL.symm)
    apply Fin.ext
    simpa [platformSyracuseResidue, Nat.ModEq] using hmod
  · exact False.elim (hex ⟨N, hreal⟩)

def platformSyracuseCrossingResidueCover
    (t q : ℕ) (hq : 0 < q) : Finset (Fin (2 ^ q)) := by
  classical
  exact (Finset.univ : Finset (platformPositivePrefixLabel t q)).image
    (platformSyracuseResidueForLabel t q hq)

lemma platformSyracuseCrossingResidueCover_card_le
    (t q : ℕ) (hq : 0 < q) :
    (platformSyracuseCrossingResidueCover t q hq).card ≤
      ∑ k : Fin t, Nat.choose (q - 1) k := by
  classical
  calc
    (platformSyracuseCrossingResidueCover t q hq).card ≤
        Fintype.card (platformPositivePrefixLabel t q) := by
      simpa [platformSyracuseCrossingResidueCover] using
        (Finset.card_image_le
          (s := (Finset.univ : Finset (platformPositivePrefixLabel t q)))
          (f := platformSyracuseResidueForLabel t q hq))
    _ = ∑ k : Fin t, Nat.choose (q - 1) k :=
      platform_card_positivePrefixLabel t q hq

lemma platformSyracuseCrossingResidueCover_mem
    (N t q : ℕ) (hN : 0 < N) (hodd : Odd N) (hq : 0 < q)
    (hsum : q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent N i) :
    platformSyracuseResidue N q hq ∈ platformSyracuseCrossingResidueCover t q hq := by
  classical
  let L := platformPositivePrefixLabelOfCrossing N t q hN hodd hq hsum
  have hreal : platformPositivePrefixLabelRealized t q hq L N :=
    ⟨hN, hodd, hsum, rfl⟩
  have hres := platformSyracuseResidueForLabel_eq_of_realized t q hq L N hreal
  rw [← hres]
  exact Finset.mem_image.mpr ⟨L, Finset.mem_univ _, rfl⟩

lemma platform_measure_finite_residue_cover_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (m : ℕ) (R : Finset (Fin m)) (U : ENNReal)
    (_hm : 0 < m)
    (hR : ∀ r ∈ R, μ {ω : Ω | N ω % m = r.val} ≤ U) :
    μ {ω : Ω | ∃ r ∈ R, N ω % m = r.val} ≤ (R.card : ENNReal) * U := by
  have hcover :
      {ω : Ω | ∃ r ∈ R, N ω % m = r.val} =
        ⋃ r ∈ R, {ω : Ω | N ω % m = r.val} := by
    ext ω
    simp
  calc
    μ {ω : Ω | ∃ r ∈ R, N ω % m = r.val} =
        μ (⋃ r ∈ R, {ω : Ω | N ω % m = r.val}) := by rw [hcover]
    _ ≤ ∑ r ∈ R, μ {ω : Ω | N ω % m = r.val} :=
      measure_biUnion_finset_le R (fun r : Fin m => {ω : Ω | N ω % m = r.val})
    _ ≤ ∑ _r ∈ R, U := by
      gcongr with r hr
      exact hR r hr
    _ = (R.card : ENNReal) * U := by simp

lemma platform_measure_subset_residue_cover_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (m : ℕ) (R : Finset (Fin m))
    (U : ENNReal) (K : ℕ) (_hm : 0 < m)
    (hR : ∀ r ∈ R, μ {ω : Ω | N ω % m = r.val} ≤ U)
    (E : Set Ω)
    (hE : ∀ ω ∈ E, ∃ r ∈ R, N ω % m = r.val)
    (hcard : R.card ≤ K) :
    μ E ≤ (K : ENNReal) * U := by
  have hsub : E ⊆ {ω : Ω | ∃ r ∈ R, N ω % m = r.val} := by
    intro ω hω
    exact hE ω hω
  have hcard' : (R.card : ENNReal) ≤ (K : ENNReal) := by
    exact_mod_cast hcard
  calc
    μ E ≤ μ {ω : Ω | ∃ r ∈ R, N ω % m = r.val} := measure_mono hsub
    _ ≤ (R.card : ENNReal) * U :=
      platform_measure_finite_residue_cover_le μ N m R U _hm hR
    _ ≤ (K : ENNReal) * U := by gcongr

theorem platform_syracuse_crossing_mass_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (t q : ℕ) (hq : 0 < q) (U : ENNReal)
    (hR : ∀ r : Fin (2 ^ q),
      μ {ω : Ω | N ω % 2 ^ q = r.val} ≤ U) :
    μ {ω : Ω |
      0 < N ω ∧ Odd (N ω) ∧
        q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent (N ω) i} ≤
      (∑ k : Fin t, Nat.choose (q - 1) k : ENNReal) * U := by
  let R : Finset (Fin (2 ^ q)) := platformSyracuseCrossingResidueCover t q hq
  let K : ℕ := ∑ k : Fin t, Nat.choose (q - 1) k
  let E : Set Ω := {ω : Ω |
    0 < N ω ∧ Odd (N ω) ∧
      q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent (N ω) i}
  have hRcard : R.card ≤ K := by
    exact platformSyracuseCrossingResidueCover_card_le t q hq
  have hE : ∀ ω ∈ E, ∃ r ∈ R, N ω % 2 ^ q = r.val := by
    intro ω hω
    have hres : platformSyracuseResidue (N ω) q hq ∈ R := by
      exact platformSyracuseCrossingResidueCover_mem (N ω) t q hω.1 hω.2.1 hq hω.2.2
    exact ⟨platformSyracuseResidue (N ω) q hq, hres, rfl⟩
  have hmass := platform_measure_subset_residue_cover_le
    μ N (2 ^ q) R U K (by positivity)
      (by intro r _hr; exact hR r) E hE hRcard
  simpa [E, K] using hmass

def syracuseExponent (N i : ℕ) : ℕ := platformSyracuseExponent N i

def platformRate (c : ℝ) : ℝ :=
  ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c))

lemma platform_rate_pos_lt_one {c : ℝ} (hc : 0 < c) :
    0 < platformRate c ∧ platformRate c < 1 := by
  let A : ℝ := (2 + c) / (2 * (1 + c))
  let B : ℝ := 1 + c
  let q : ℝ := 2 + c
  have hq : 0 < q := by dsimp [q]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hpowpos : 0 < Real.rpow B q⁻¹ := Real.rpow_pos_of_pos hB _
  have hpos : 0 < A * Real.rpow B q⁻¹ := mul_pos hA hpowpos
  have hs : -1 ≤ c / q := by
    have : 0 ≤ c / (2 + c) := by positivity
    dsimp [q]
    linarith
  have hs' : c / q ≠ 0 := by
    dsimp [q]
    positivity
  have hbern : 1 + q * (c / q) < (1 + c / q) ^ q :=
    one_add_mul_self_lt_rpow_one_add hs hs' (by dsimp [q]; linarith)
  have hbern' : B < (A⁻¹) ^ q := by
    have hleft : 1 + q * (c / q) = B := by
      dsimp [B, q]
      field_simp [hq.ne']
    have hright : 1 + c / q = A⁻¹ := by
      dsimp [A, q]
      field_simp [hA.ne', hq.ne']
      ring
    rw [hleft, hright] at hbern
    exact hbern
  have hpow : Real.rpow B q⁻¹ < A⁻¹ := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hB.le _) (by positivity) hq).mp
    rw [← Real.rpow_mul (by positivity : 0 ≤ B)]
    rw [inv_mul_cancel₀ hq.ne', Real.rpow_one]
    exact hbern'
  constructor
  · simpa [platformRate, A, B, q, one_div] using hpos
  · have hpow' : Real.rpow B q⁻¹ < 1 / A := by simpa [one_div] using hpow
    have hmul : Real.rpow B q⁻¹ * A < 1 := (lt_div_iff₀ hA).mp hpow'
    simpa [platformRate, A, B, q, one_div, mul_comm] using hmul

lemma platform_ennreal_prefix_bound
    (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (q t : ℕ) (hq : 0 < q)
    (hqt : (2 + c) * (t : ℝ) ≤ (q : ℝ)) :
    (∑ k : Fin t, (Nat.choose (q - 1) k : ENNReal)) *
        ENNReal.ofReal ((K + 2) / (2 : ℝ) ^ q) ≤
      ENNReal.ofReal ((K + 2) * (platformRate c) ^ q) := by
  have htail := binomial_prefix_tail_of_linear_gap c hc q t hq hqt
  have hsum :
      ENNReal.ofReal (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) =
        ∑ k : Fin t, (Nat.choose (q - 1) k : ENNReal) := by
    simpa using
      (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ)
        (f := fun k : Fin t => (Nat.choose (q - 1) k : ℝ))
        (by intro k hk; positivity))
  have hreal :
      (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) *
          ((K + 2) / (2 : ℝ) ^ q) ≤
        (K + 2) * (platformRate c) ^ q := by
    have htail' :
        (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) / (2 : ℝ) ^ q ≤
          (platformRate c) ^ q := by
      simpa [platformRate] using htail.2.2
    calc
      (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) *
            ((K + 2) / (2 : ℝ) ^ q) =
          (K + 2) * ((∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) /
            (2 : ℝ) ^ q) := by ring
      _ ≤ (K + 2) * (platformRate c) ^ q :=
        mul_le_mul_of_nonneg_left htail' (by linarith)
  calc
    (∑ k : Fin t, (Nat.choose (q - 1) k : ENNReal)) *
          ENNReal.ofReal ((K + 2) / (2 : ℝ) ^ q) =
        ENNReal.ofReal ((∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) *
          ((K + 2) / (2 : ℝ) ^ q)) := by
      rw [← hsum, ← ENNReal.ofReal_mul]
      positivity
    _ ≤ ENNReal.ofReal ((K + 2) * (platformRate c) ^ q) :=
      ENNReal.ofReal_le_ofReal hreal

theorem solution
    (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ A d : ℝ, 0 < A ∧ 0 < d ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ),
        Measurable N →
        (∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) →
        ∀ q t : ℕ, 0 < q →
          (2 + c) * (t : ℝ) ≤ (q : ℝ) →
          (∑ r : Fin (2 ^ q),
            |(μ {ω : Ω | N ω % 2 ^ q = r.val}).toReal -
              (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| ≤
            K / (2 : ℝ) ^ q) →
          μ {ω : Ω |
            q ≤ ∑ i ∈ Finset.range t,
              (3 * (syracuseStep^[i]) (N ω) + 1).factorization 2} ≤
            ENNReal.ofReal (A * Real.exp (-d * (t : ℝ))) := by
  have hrate := platform_rate_pos_lt_one hc
  have hlog : Real.log (platformRate c) < 0 := Real.log_neg hrate.1 hrate.2
  let d : ℝ := -(2 + c) * Real.log (platformRate c)
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos_of_neg_of_neg (by linarith) hlog
  refine ⟨K + 3, d, by linarith, hd, ?_⟩
  intro Ω _inst μ _instProb N _hN hAE q t hq hqt hL1
  have hR : ∀ r : Fin (2 ^ q),
      μ {ω : Ω | N ω % 2 ^ q = r.val} ≤
        ENNReal.ofReal ((K + 2) / (2 : ℝ) ^ q) := by
    intro r
    let p : ℝ := (μ {ω : Ω | N ω % 2 ^ q = r.val}).toReal
    let u : ℝ := if Odd r.val then 2 / (2 : ℝ) ^ q else 0
    have hterm :
        |p - u| ≤ ∑ s : Fin (2 ^ q),
          |(μ {ω : Ω | N ω % 2 ^ q = s.val}).toReal -
            (if Odd s.val then 2 / (2 : ℝ) ^ q else 0)| := by
      apply Finset.single_le_sum (s := (Finset.univ : Finset (Fin (2 ^ q))))
        (f := fun s : Fin (2 ^ q) =>
          |(μ {ω : Ω | N ω % 2 ^ q = s.val}).toReal -
            (if Odd s.val then 2 / (2 : ℝ) ^ q else 0)|)
      · intro s hs; exact abs_nonneg _
      · exact Finset.mem_univ r
    have hdev : |p - u| ≤ K / (2 : ℝ) ^ q := by
      simpa [p, u] using hterm.trans hL1
    have hbase : u ≤ 2 / (2 : ℝ) ^ q := by
      dsimp [u]
      split_ifs
      · exact le_rfl
      · positivity
    have hreal : p ≤ (K + 2) / (2 : ℝ) ^ q := by
      have hdiff : p - u ≤ |p - u| := le_abs_self _
      calc
        p ≤ u + |p - u| := by linarith
        _ ≤ 2 / (2 : ℝ) ^ q + K / (2 : ℝ) ^ q := add_le_add hbase hdev
        _ = (K + 2) / (2 : ℝ) ^ q := by ring
    have hfinite : μ {ω : Ω | N ω % 2 ^ q = r.val} ≠ ⊤ := measure_ne_top μ _
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal
  have hF := platform_syracuse_crossing_mass_le
    μ N t q hq (ENNReal.ofReal ((K + 2) / (2 : ℝ) ^ q)) hR
  have hF' := hF.trans (platform_ennreal_prefix_bound c K hc hK q t hq hqt)
  have hpow := binomial_prefix_tail_of_linear_gap c hc q t hq hqt
  have hpow' :
      (platformRate c) ^ q ≤ Real.exp (-d * (t : ℝ)) := by
    have hqlog :
        (q : ℝ) * Real.log (platformRate c) ≤
          (2 + c) * (t : ℝ) * Real.log (platformRate c) := by
      exact mul_le_mul_of_nonpos_right hqt hlog.le
    have hexp :
        Real.exp ((q : ℝ) * Real.log (platformRate c)) ≤
          Real.exp ((2 + c) * (t : ℝ) * Real.log (platformRate c)) :=
      Real.exp_le_exp.mpr hqlog
    have hpowexp :
        (platformRate c) ^ q = Real.exp ((q : ℝ) * Real.log (platformRate c)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hrate.1]
      congr 1
      ring
    rw [hpowexp]
    calc
      Real.exp ((q : ℝ) * Real.log (platformRate c)) ≤
          Real.exp ((2 + c) * (t : ℝ) * Real.log (platformRate c)) := hexp
      _ = Real.exp (-d * (t : ℝ)) := by
        congr 1
        dsimp [d]
        ring
  have hreal :
      (K + 2) * (platformRate c) ^ q ≤
        (K + 3) * Real.exp (-d * (t : ℝ)) := by
    calc
      (K + 2) * (platformRate c) ^ q ≤
          (K + 2) * Real.exp (-d * (t : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow' (by linarith)
      _ ≤ (K + 3) * Real.exp (-d * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
  have hF'' :
      μ {ω : Ω |
        0 < N ω ∧ Odd (N ω) ∧
          q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent (N ω) i} ≤
        ENNReal.ofReal ((K + 3) * Real.exp (-d * (t : ℝ))) :=
    hF'.trans (ENNReal.ofReal_le_ofReal hreal)
  have hAEsub :
      {ω : Ω | q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent (N ω) i} ≤ᵐ[μ]
        {ω : Ω |
          0 < N ω ∧ Odd (N ω) ∧
            q ≤ ∑ i ∈ Finset.range t, platformSyracuseExponent (N ω) i} := by
    filter_upwards [hAE] with ω hω hsum
    exact ⟨hω.1, hω.2, hsum⟩
  simpa [platformSyracuseExponent] using (measure_mono_ae hAEsub).trans hF''
