-- Prove2me | solution 1 for ledoux_talagrand_finite_bool_product_linear_process_good_event_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T06:34:59.058643+00:00
-- url     : https://prove2.me/submissions/9e868d16-8502-4d6e-b6f3-39521ba7d11d

import Theorems.Thm_candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail
import Mathlib.Tactic

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

/-!
Source: formal complement bridge from the Candès--Romberg bad-event theorem to
the Ledoux--Talagrand good-event theorem.

Analytic source: Ledoux, *The Concentration of Measure Phenomenon*, Section 7,
Corollary 7.8.  Candès--Romberg, *Sparsity and incoherence in compressive
sampling*, PDF p. 11, Section 3, Theorem 3.2/equation (3.9), states the
equivalent bad-event form, and Candès--Recht, *Exact Matrix Completion via
Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1/equations
(9.1)--(9.2), cites this input.  This sketch contains no analytic
concentration argument: it only uses the probability identity
`μ(Gᶜ) = 1 - μ(G)` to convert the source bad-event bound into the displayed
good-event lower bound.
-/
theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (κ : Type) [Fintype κ] (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → κ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ x : κ, |coeff a x| ≤ B) →
        (∀ a : ι,
          ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * (coeff a x) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → (κ → Bool) → ℝ :=
          fun a ω =>
            ∑ x : κ, ((cond (ω x) (1 : ℝ) 0 - (p : ℝ)) * coeff a x)
        let boolZ : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)).real
            {ω | |boolZ ω -
                  (∫ ω, boolZ ω
                    ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))| ≤ t} ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B *
                      (∫ ω, boolZbar ω
                        ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))))) := by
  classical
  rcases candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail with
    ⟨K, hK, hBadTail⟩
  refine ⟨K, hK, ?_⟩
  intro κ _instFintype p hp ι _instFintypeι _instNonempty coeff B sigmaSq t
    hB hsigma ht hbound hvar
  let μ := Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)
  let boolProcess : ι → (κ → Bool) → ℝ :=
    fun a ω =>
      ∑ x : κ, ((cond (ω x) (1 : ℝ) 0 - (p : ℝ)) * coeff a x)
  let boolZ : (κ → Bool) → ℝ :=
    fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
  let boolZbar : (κ → Bool) → ℝ :=
    fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
  let failure : ℝ :=
    3 * Real.exp
      (-(t / (K * B)) *
        Real.log
          (1 + (B * t) /
            (sigmaSq + B * (∫ ω, boolZbar ω ∂μ))))
  let Good : Set (κ → Bool) :=
    {ω | |boolZ ω - (∫ ω, boolZ ω ∂μ)| ≤ t}
  let Bad : Set (κ → Bool) :=
    {ω | ¬ |boolZ ω - (∫ ω, boolZ ω ∂μ)| ≤ t}
  have hBad : μ.real Bad ≤ failure := by
    simpa [μ, boolProcess, boolZ, boolZbar, failure, Bad] using
      hBadTail κ p hp ι coeff B sigmaSq t hB hsigma ht hbound hvar
  have hBad_eq : Bad = Goodᶜ := by
    ext ω
    rfl
  have hGoodMeas : MeasurableSet Good :=
    MeasurableSet.of_discrete
  have hcompl : μ.real Bad = 1 - μ.real Good := by
    rw [hBad_eq]
    exact probReal_compl_eq_one_sub (μ := μ) hGoodMeas
  have hGood : μ.real Good ≥ 1 - failure := by
    rw [hcompl] at hBad
    linarith
  simpa [μ, boolProcess, boolZ, boolZbar, failure, Good] using hGood
