-- Prove2me | solution 1 for gpy_singSum_grouped
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T17:11:29.951634+00:00
-- url     : https://prove2.me/submissions/5467c98d-9f52-44f8-9d6d-1b4e0998bf8d

/-
  Submission file for the Prove2Me problem `gpy_singSum_grouped`
  (Selberg singular sum in grouped form over moduli).

  Self-contained: imports Mathlib only. Contains the verified bodies
  needed for the grouped form (support, good pairs, Selberg weight and
  its expansion, singular sum, monomial pair sums, modulus grouping,
  squarefree vanishing, admissibility/local-factor definitions, and
  the local-factor identity), the restated theorem, and top-level
  `theorem solution` in the problem's exact binder/statement form
  (statement mechanically extracted from the restated theorem, so the
  two are textually identical). The full singular-series evaluation
  to S(h) times an integral is NOT proved here and is NOT claimed.
  No sorry tactic, no axioms beyond the standard ones, no platform
  imports.
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace GPY

def tupleSupport (k : ℕ) (R : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)

theorem mem_tupleSupport {k : ℕ} {R : ℕ} {d : Fin k → ℕ} :
    d ∈ tupleSupport k R ↔
      (∀ i, 1 ≤ d i) ∧ (∀ i, d i ≤ R) ∧ ∏ i, d i ≤ R := by
  rw [tupleSupport, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (Finset.mem_Icc.mp (h1 i)).1,
      fun i => (Finset.mem_Icc.mp (h1 i)).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, h2 i⟩, h3⟩

def goodPair {k : ℕ} (h d e : Fin k → ℕ) (i : Fin k) : Prop :=
  ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))

noncomputable def lamSelberg (k : ℕ) (R : ℕ) (deg : ℕ) (d : Fin k → ℕ) : ℝ :=
  if ∏ i, d i ≤ R then
    (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
      * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
  else 0

theorem lamSelberg_eq_of_mem_support {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) :
    lamSelberg k R deg d
      = (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg := by
  unfold lamSelberg
  rw [if_pos (mem_tupleSupport.mp hd).2.2]

theorem one_sub_pow_expand (t : ℝ) (deg : ℕ) :
    (1 - t) ^ deg = ∑ j ∈ Finset.range (deg + 1),
      (deg.choose j : ℝ) * (-t) ^ j := by
  have h1 : (1 - t) ^ deg = ∑ k ∈ Finset.range (deg + 1),
      (deg.choose k : ℝ) * (-t) ^ (deg - k) := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, one_mul, mul_comm]
  rw [h1]
  rw [← Finset.sum_range_reflect
    (fun j => (deg.choose j : ℝ) * (-t) ^ j) (deg + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkk : k ≤ deg := by omega
  have hdeg : deg + 1 - 1 - k = deg - k := by omega
  rw [hdeg, Nat.choose_symm hkk]

theorem lamSelberg_expand {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) :
    lamSelberg k R deg d = ∑ j ∈ Finset.range (deg + 1),
      (deg.choose j : ℝ) * (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (-(Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R)) ^ j := by
  rw [lamSelberg_eq_of_mem_support hd, one_sub_pow_expand]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sum_comm4 {α γ : Type*} {s : Finset α} {t : Finset γ}
    (F : α → α → γ → γ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := by
  have h1 : ∀ d : α, (∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ e ∈ s, ∑ b ∈ t, F d e a b := by
    intro d
    exact Finset.sum_comm
  have h2 : (∑ d ∈ s, ∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b := by
    calc _ = ∑ d ∈ s, ∑ a ∈ t, ∑ e ∈ s, ∑ b ∈ t, F d e a b :=
          Finset.sum_congr rfl (fun d _ => h1 d)
      _ = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b :=
          Finset.sum_comm
  have h3 : ∀ a : γ, (∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b)
      = ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := by
    intro a
    calc _ = ∑ d ∈ s, ∑ b ∈ t, ∑ e ∈ s, F d e a b := by
          apply Finset.sum_congr rfl
          intro d _
          exact Finset.sum_comm
      _ = ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := Finset.sum_comm
  calc _ = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b := h2
    _ = ∑ a ∈ t, ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b :=
        Finset.sum_congr rfl (fun a _ => h3 a)

theorem sum_sum_sum_comm {α γ : Type*} {s : Finset α} {u : Finset γ}
    (F : α → α → γ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, ∑ i ∈ u, F d e i)
      = ∑ i ∈ u, ∑ d ∈ s, ∑ e ∈ s, F d e i := by
  calc (∑ d ∈ s, ∑ e ∈ s, ∑ i ∈ u, F d e i)
      = ∑ p ∈ s ×ˢ s, ∑ i ∈ u, F p.1 p.2 i :=
        (Finset.sum_product' (s := s) (t := s)
          (f := fun d e => ∑ i ∈ u, F d e i)).symm
    _ = ∑ i ∈ u, ∑ p ∈ s ×ˢ s, F p.1 p.2 i := Finset.sum_comm
    _ = ∑ i ∈ u, ∑ d ∈ s, ∑ e ∈ s, F d e i := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_product' (s := s) (t := s) (f := fun d e => F d e i)

noncomputable def singSum (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) : ℝ := by
  classical
  exact ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if goodPair h d e i then lam d * lam e
      / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
    else 0

noncomputable def monomialPairSum (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if goodPair h d e i then
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
    else 0

noncomputable def monomialPairSumAtL (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
      ∧ goodPair h d e i)
    then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
    else 0

theorem lcm_le_sq_of_mem_support {k : ℕ} {R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) (he : e ∈ tupleSupport k R) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≤ R ^ 2 := by
  classical
  have hd1 : ∀ j, 1 ≤ d j := (mem_tupleSupport.mp hd).1
  have hdprod : ∏ j, d j ≤ R := (mem_tupleSupport.mp hd).2.2
  have he1 : ∀ j, 1 ≤ e j := (mem_tupleSupport.mp he).1
  have heprod : ∏ j, e j ≤ R := (mem_tupleSupport.mp he).2.2
  have hmne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 := by
    intro j
    apply Nat.lcm_ne_zero
    · have h1 := hd1 j
      omega
    · have h2 := he1 j
      omega
  have hprodpos : 0 < ∏ j, Nat.lcm (d j) (e j) :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hmne j))
  have hdvd : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ∣ ∏ j, Nat.lcm (d j) (e j) :=
    Finset.lcm_dvd (fun j _ => Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  have hle1 : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ≤ ∏ j, Nat.lcm (d j) (e j) :=
    Nat.le_of_dvd hprodpos hdvd
  have hle2 : ∏ j, Nat.lcm (d j) (e j) ≤ ∏ j, (d j * e j) := by
    apply Finset.prod_le_prod'
    intro j _
    have h1 : GCDMonoid.lcm (d j) (e j) ∣ d j * e j :=
      lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _)
    rw [lcm_eq_nat_lcm] at h1
    exact Nat.le_of_dvd (mul_pos (by have h := hd1 j; omega) (by have h := he1 j; omega)) h1
  have hle3 : ∏ j, (d j * e j) = (∏ j, d j) * (∏ j, e j) := Finset.prod_mul_distrib
  have hle4 : (∏ j, d j) * (∏ j, e j) ≤ R * R := Nat.mul_le_mul hdprod heprod
  calc Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ≤ ∏ j, Nat.lcm (d j) (e j) := hle1
    _ ≤ ∏ j, (d j * e j) := hle2
    _ = (∏ j, d j) * (∏ j, e j) := hle3
    _ ≤ R * R := hle4
    _ = R ^ 2 := (pow_two R).symm

theorem monomialPairSum_eq_sum_over_L {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    monomialPairSum k h R a b i
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  have hmem : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
        ∈ Finset.Icc 1 (R ^ 2) := by
    intro d hd e he
    obtain ⟨h1, -, -⟩ := mem_tupleSupport.mp hd
    obtain ⟨h1', -, -⟩ := mem_tupleSupport.mp he
    have hLne : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≠ 0 := by
      apply Finset.lcm_ne_zero_iff.mpr
      intro j _
      apply Nat.lcm_ne_zero
      · have hj := h1 j
        omega
      · have hj := h1' j
        omega
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hLne, lcm_le_sq_of_mem_support hd he⟩
  have hstep1 : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (if goodPair h d e i then
        (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0)
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0) := by
    intro d hd e he
    rw [Finset.sum_ite_eq', if_pos (hmem d hd e he)]
  have hstep3 : ∀ L ∈ Finset.Icc 1 (R ^ 2),
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0))
      = (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
    intro L _
    have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0)
        = (1 / ((Nat.totient L : ℕ) : ℝ)) *
          (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
      intro d _ e _
      by_cases hLe : L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      · by_cases hg : goodPair h d e i
        · rw [if_pos hLe, if_pos hg, if_pos ⟨hLe.symm, hg⟩,
            mul_comm (1 / ((Nat.totient L : ℕ) : ℝ)) _, mul_one_div]
        · rw [if_pos hLe, if_neg hg, if_neg (fun hcon => hg hcon.2), mul_zero]
      · rw [if_neg hLe, if_neg (fun hcon => hLe hcon.1.symm), mul_zero]
    rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))]
    unfold monomialPairSumAtL
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  unfold monomialPairSum
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hstep1 d hd e he))]
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl (fun L hL => hstep3 L hL)

theorem singSum_selberg_expand {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i := by
  have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (if goodPair h d e i then lamSelberg k R deg d * lamSelberg k R deg e
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0) := by
    intro d hd e he
    by_cases hg : goodPair h d e i
    · rw [if_pos hg]
      rw [lamSelberg_expand hd, lamSelberg_expand he, Finset.sum_mul_sum]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      rw [if_pos hg]
      ring
    · rw [if_neg hg]
      simp only [if_neg hg, mul_zero, Finset.sum_const_zero]
  have h2 : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      (if goodPair h d e i then lamSelberg k R deg d * lamSelberg k R deg e
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0))
      = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0) :=
    Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))
  have hfactor : ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0))
      = (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i := by
    intro a _ b _
    unfold monomialPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  unfold singSum
  rw [h2, sum_comm4]
  exact Finset.sum_congr rfl
    (fun a ha => Finset.sum_congr rfl (fun b hb => hfactor a ha b hb))

theorem singSum_selberg_grouped {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  rw [singSum_selberg_expand]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [monomialPairSum_eq_sum_over_L]

theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le (Squarefree.natFactorization_le_one p ha)
    (Squarefree.natFactorization_le_one p hb)

theorem squarefree_finset_lcm {ι : Type*} {s : Finset ι} {g : ι → ℕ}
    (h0 : ∀ j ∈ s, g j ≠ 0) (hsq : ∀ j ∈ s, Squarefree (g j)) :
    Squarefree (s.lcm g) := by
  apply Nat.squarefree_of_factorization_le_one (Finset.lcm_ne_zero_iff.mpr h0)
  intro p
  rw [Finset.factorization_lcm h0 p]
  apply Finset.sup_le
  intro j hj
  exact Squarefree.natFactorization_le_one p (hsq j hj)

theorem monomialPairSumAtL_eq_zero_of_not_squarefree {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) {L : ℕ} (hL : ¬ Squarefree L) :
    monomialPairSumAtL k h R a b i L = 0 := by
  unfold monomialPairSumAtL
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  by_cases hcon : (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
    ∧ goodPair h d e i)
  · rw [if_pos hcon]
    obtain ⟨hd1, -, -⟩ := mem_tupleSupport.mp hd
    obtain ⟨he1, -, -⟩ := mem_tupleSupport.mp he
    have hLnsq : ¬ Squarefree (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) := by
      rw [hcon.1]
      exact hL
    have h0 : ∀ j ∈ (Finset.univ : Finset (Fin k)), Nat.lcm (d j) (e j) ≠ 0 := by
      intro j _
      apply Nat.lcm_ne_zero
      · have hj := hd1 j
        omega
      · have hj := he1 j
        omega
    have hex : ∃ j, ¬ Squarefree (Nat.lcm (d j) (e j)) := by
      by_contra hnone
      push Not at hnone
      exact hLnsq (squarefree_finset_lcm h0 (fun j _ => hnone j))
    obtain ⟨j, hj⟩ := hex
    by_cases hdjsq : Squarefree (d j)
    · have hejsq : ¬ Squarefree (e j) := fun hh => hj (squarefree_lcm hdjsq hh)
      have hE : ¬ Squarefree (∏ j, e j) := fun hsq =>
        hejsq (hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem (fun j => e j) (Finset.mem_univ j)))
      have hmu : (ArithmeticFunction.moebius (∏ j, e j) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hE
      rw [hmu]
      simp
    · have hD : ¬ Squarefree (∏ j, d j) := fun hsq =>
        hdjsq (hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem (fun j => d j) (Finset.mem_univ j)))
      have hmu : (ArithmeticFunction.moebius (∏ j, d j) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hD
      rw [hmu]
      simp
  · rw [if_neg hcon]

def residueCount {k : ℕ} (h : Fin k → ℕ) (p : ℕ) : ℕ :=
  (Finset.univ.image (fun i => h i % p)).card

def Admissible {k : ℕ} (h : Fin k → ℕ) : Prop :=
  ∀ p, Nat.Prime p → residueCount h p < p

noncomputable def localFactor {k : ℕ} (h : Fin k → ℕ) (p : ℕ) : ℝ :=
  (1 - (residueCount h p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ k

noncomputable def singSeriesTrunc {k : ℕ} (h : Fin k → ℕ) (P : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (P + 1)).filter Nat.Prime, localFactor h p

theorem singSum_selberg_grouped_restated {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) *
              (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                  ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                    * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                    * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                    * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                else 0) := by
  have hmain := singSum_selberg_grouped h R deg i
  unfold singSum lamSelberg tupleSupport goodPair monomialPairSumAtL at hmain
  exact hmain

end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) *
              (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                  ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                    * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                    * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                    * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                else 0) := GPY.singSum_selberg_grouped_restated h R deg i
