-- Prove2me | solution 1 for ledoux_talagrand_finite_bool_product_coordinate_process_good_event_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T04:29:09.086598+00:00
-- url     : https://prove2.me/submissions/cc57efdf-6f18-4b97-9f8d-e5a8f0a50d55

import Theorems.Thm_ledoux_talagrand_finite_bool_product_linear_process_good_event_log_tail
import Mathlib.Tactic

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

/-!
Source: formal specialization bridge from the generic finite Boolean
product-measure Ledoux--Talagrand good-event theorem to the matrix-coordinate
product index set.  The analytic source is Ledoux, *The Concentration of
Measure Phenomenon*, Section 7, Corollary 7.8; Candes--Romberg, *Sparsity and
incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2,
equation (3.9); cited by Candes--Recht, *Exact Matrix Completion via Convex
Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations
(9.1)--(9.2).  This sketch contains no new concentration argument: it only
specializes the generic coordinate type to `Fin n₁ × Fin n₂`, unfolds
`bernMeasure`, and rewrites the pair-indexed sum as the double sum over
matrix coordinates.
-/

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ : ℕ) (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (p : ℝ) * (1 - (p : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun a ω =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              ((cond (ω (i, j)) (1 : ℝ) 0 - (p : ℝ)) * coeff a i j)
        let boolZ : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (bernMeasure (n1 := n₁) (n2 := n₂) p hp).real
            {ω | |boolZ ω -
                  (∫ ω, boolZ ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))| ≤ t} ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B *
                      (∫ ω, boolZbar ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))))) := by
  classical
  rcases ledoux_talagrand_finite_bool_product_linear_process_good_event_log_tail with
    ⟨K, hK, hLinear⟩
  refine ⟨K, hK, ?_⟩
  intro n₁ n₂ p hp ι _instFintype _instNonempty coeff B sigmaSq t
    hB hsigma ht hbound hvar
  let coeffPair : ι → (Fin n₁ × Fin n₂) → ℝ :=
    fun a x => coeff a x.1 x.2
  have hboundPair : ∀ a : ι, ∀ x : Fin n₁ × Fin n₂, |coeffPair a x| ≤ B := by
    intro a x
    exact hbound a x.1 x.2
  have hvarPair :
      ∀ a : ι,
        ∑ x : Fin n₁ × Fin n₂,
          (p : ℝ) * (1 - (p : ℝ)) * (coeffPair a x) ^ 2 ≤ sigmaSq := by
    intro a
    simpa [coeffPair, Fintype.sum_prod_type] using hvar a
  have hSpec :=
    hLinear (Fin n₁ × Fin n₂) p hp ι coeffPair B sigmaSq t
      hB hsigma ht hboundPair hvarPair
  simpa [bernMeasure, coeffPair, Fintype.sum_prod_type] using hSpec
