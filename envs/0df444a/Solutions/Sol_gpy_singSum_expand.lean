-- Prove2me | solution 1 for gpy_singSum_expand
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T19:54:18.80292+00:00
-- url     : https://prove2.me/submissions/526b4dc6-eb33-4cfa-beb7-2a28ce98c407

/-
  Submission file for the Prove2Me problem `gpy_singSum_expand`
  (Selberg singular sum: exact monomial-pair decomposition).

  Self-contained: imports Mathlib only. Contains the verified bodies
  needed for the expansion (support, good pairs, Selberg weight and
  its expansion, singular sum, monomial pair sums, squarefree
  vanishing), the restated theorem, and top-level `theorem solution`
  in the problem's exact binder/statement form (statement mechanically
  extracted from the restated theorem, so the two are textually
  identical). This is the UNGROUPED monomial decomposition; it is
  distinct from the grouped forms (by modulus) submitted separately.
  The full singular-series evaluation to S(h) times an integral is NOT
  proved here and is NOT claimed.
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

theorem monomialPairSum_summand_eq_zero_of_not_squarefree {k : ℕ}
    (h : Fin k → ℕ) (R : ℕ) (a b : ℕ) (i : Fin k)
    {d e : Fin k → ℕ} (hd : ¬ Squarefree (∏ j, d j)) :
    (if goodPair h d e i then
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
     else 0) = 0 := by
  by_cases hg : goodPair h d e i
  · rw [if_pos hg]
    have hmu : (ArithmeticFunction.moebius (∏ j, d j) : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
    rw [hmu]
    simp
  · rw [if_neg hg]

theorem monomialPairSum_summand_eq_zero_of_not_squarefree_right {k : ℕ}
    (h : Fin k → ℕ) (R : ℕ) (a b : ℕ) (i : Fin k)
    {d e : Fin k → ℕ} (he : ¬ Squarefree (∏ j, e j)) :
    (if goodPair h d e i then
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
     else 0) = 0 := by
  by_cases hg : goodPair h d e i
  · rw [if_pos hg]
    have hmu : (ArithmeticFunction.moebius (∏ j, e j) : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree he
    rw [hmu]
    simp
  · rw [if_neg hg]

theorem singSum_selberg_expand_restated {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
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
          (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
            else 0) := by
  have hmain := singSum_selberg_expand h R deg i
  unfold singSum lamSelberg tupleSupport goodPair monomialPairSum at hmain
  exact hmain

end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
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
          (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
            else 0) := GPY.singSum_selberg_expand_restated h R deg i

#print axioms solution
