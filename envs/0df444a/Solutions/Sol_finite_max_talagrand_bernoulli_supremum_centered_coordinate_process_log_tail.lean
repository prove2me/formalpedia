-- Prove2me | solution 1 for finite_max_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T20:11:33.512933+00:00
-- url     : https://prove2.me/submissions/18aff894-d064-4a6f-90dc-247be5dfec9c

import Theorems.Thm_ledoux_talagrand_finite_bernoulli_coordinate_process_log_tail

open MatrixCompletion
open scoped Classical BigOperators

/-!
Source: Candes--Recht Appendix 9.1, PDF p. 46, Theorem 9.1, uses a symmetric
test-function class.  The analytic concentration input is the textbook
Talagrand--Ledoux empirical-process theorem, cited there as Talagrand [33] and
also in Candes--Romberg, PDF p. 11, as Ledoux, *The Concentration of Measure
Phenomenon*, Section 7, Corollary 7.8.

This sketch is a purely formal bridge from the Ledoux--Talagrand
absolute-supremum statement to the finite symmetric Candes--Recht leaf.  The
only bridge step is the standard identity
`max_a |S_a| = max_a S_a` when the finite class is closed under negation.
-/

private lemma finite_sup_abs_eq_sup_of_neg_closed
    {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ)
    (hneg : ∀ a : ι, ∃ a' : ι, v a' = -v a) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |v a|) =
      Finset.univ.sup' Finset.univ_nonempty v := by
  apply le_antisymm
  · refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro a ha
    by_cases hv : 0 ≤ v a
    · rw [abs_of_nonneg hv]
      exact Finset.le_sup' v (Finset.mem_univ a)
    · have hle : v a ≤ 0 := le_of_not_ge hv
      rcases hneg a with ⟨a', ha'⟩
      rw [abs_of_nonpos hle, ← ha']
      exact Finset.le_sup' v (Finset.mem_univ a')
  · refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro a ha
    exact (le_abs_self (v a)).trans
      (Finset.le_sup' (fun a : ι => |v a|) (Finset.mem_univ a))

private lemma finite_process_Zbar_eq_Z_of_neg_closed
    {n₁ n₂ : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (process : ι → Finset (Fin n₁ × Fin n₂) → ℝ)
    (hneg : ∀ a : ι, ∃ a' : ι, ∀ Omega, process a' Omega = -process a Omega) :
    (fun Omega =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : ι => |process a Omega|)) =
      (fun Omega =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : ι => process a Omega)) := by
  funext Omega
  refine finite_sup_abs_eq_sup_of_neg_closed (fun a => process a Omega) ?_
  intro a
  rcases hneg a with ⟨a', ha'⟩
  exact ⟨a', ha' Omega⟩

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeff a' i j = -coeff a i j) →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun a : ι =>
                ∑ i : Fin n₁, ∑ j : Fin n₂,
                  (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                    coeff a i j))
        bernoulliEventProb p
            (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B * bernoulliExpectation p Z))) := by
  rcases ledoux_talagrand_finite_bernoulli_coordinate_process_log_tail with
    ⟨K, hKpos, hLedoux⟩
  refine ⟨K, hKpos, ?_⟩
  intro n₁ n₂ m ι _instFintype _instNonempty coeff B sigmaSq t
    hn₁ hn₂ hm hB hsigma ht hsym hbound hvar
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let process : ι → Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun a Omega =>
      ∑ i : Fin n₁, ∑ j : Fin n₂,
        (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
          coeff a i j)
  let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Omega)
  let Zbar : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega =>
      Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |process a Omega|)
  have hProcessNeg : ∀ a : ι, ∃ a' : ι, ∀ Omega, process a' Omega = -process a Omega := by
    intro a
    rcases hsym a with ⟨a', ha'⟩
    refine ⟨a', ?_⟩
    intro Omega
    simp [process, p, ha', Finset.sum_neg_distrib]
  have hZbarZ : Zbar = Z :=
    finite_process_Zbar_eq_Z_of_neg_closed process hProcessNeg
  have hLedouxInst :=
    hLedoux n₁ n₂ m ι coeff B sigmaSq t hn₁ hn₂ hm hB hsigma ht hbound hvar
  simpa [p, process, Z, Zbar, hZbarZ] using hLedouxInst
