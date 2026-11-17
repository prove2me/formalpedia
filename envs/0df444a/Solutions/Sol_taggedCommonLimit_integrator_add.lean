-- Prove2me | solution 1 for taggedCommonLimit_integrator_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:22:05.246963+00:00
-- url     : https://prove2.me/submissions/c24fc4f4-eff7-4b36-a04c-f67302504521

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F000
import Mathlib.Tactic


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
open Finset
open Set

noncomputable section

section Thm_1_3_helper

/-
 If α₁ and α₂ are monotonic, then α₁ + α₂ is also monotonic
-/

/-
Additivity of upper sum when α can be decomposed as α₁ + α₂
-/

/-
Additivity of lower sum when α can be decomposed as α₁ + α₂
-/

/-
Additivity of tagged sum when α can be decomposed as α₁ + α₂
-/

/-
  Additivity of integrator for the common value of upper and lower limit
-/

/-
  Additivity of integrator for the tagged common limit
-/
theorem solution {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f α₁ L₁)
    (h₂ : TaggedCommonLimit a b f α₂ L₂) :
    TaggedCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P tags htags hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hadd :
      taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
        (taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂) := by
    rw [taggedSum_integrator_add]
    ring
  calc
    |taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
        |(taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| :=
      abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| <
            eps / 2 + eps / 2 := add_lt_add hP₁ hP₂
      simpa using hlt
end Thm_1_3_helper

section Theorem_1_3

/- # Theorem 1.3 (Existence of witness)
  If f is RS integrable w.r.t. α₁ and α₂ on the interval [a,b],
  then f is RS integral w.r.t. α₁ + α₂.
-/

/-
 # Theorem 1.3. (additivity)
 `∫ f d(α₁ + α₂) = ∫ f dα₁ + ∫ f dα₂`

Additivity of the Riemann-Stieltjes integral with respect to the integrator. (Theorem 1.3)

If a function `f` is Riemann-Stieltjes integrable with respect to both `α₁` and `α₂`
on `[a, b]`, then it is also integrable with respect to their sum `α₁ + α₂`, and the
integral evaluates exactly to the sum of the individual integrals.

*Proof Idea:*
This theorem mirrors the additivity of the integrand (Theorem 1.2, Part 1).
At the discrete level of Riemann-Stieltjes sums, the intervals distribute perfectly:
`Δ(α₁ + α₂)_i = Δ(α₁)_i + Δ(α₂)_i`. Therefore, any tagged sum over `α₁ + α₂` splits
exactly into a tagged sum over `α₁` plus a tagged sum over `α₂`.

We previously established that the limit of these combined sums converges to
`(∫ f dα₁) + (∫ f dα₂)` via `taggedCommonLimit_integrator_add`. By invoking the
uniqueness of tagged limits (`taggedCommonLimit_unique`), we mathematically seal
the equality.
-/

end Theorem_1_3

section integrator_scalar_multiply

/-!
  # Linearity of the Integrator: Scalar Multiplication

  This section establishes that the Riemann-Stieltjes integral is linear with
  respect to scalar multiplication of the integrator. Specifically, it proves that
  ∫ f d(k * α) = k * ∫ f dα.

  ## Mathematical Context
  In the standard textbook development of the Riemann-Stieltjes integral, the
  integrator `α` is required to be monotonically increasing. This guarantees that
  the width of every partition subinterval `Δα_i = α(x_{i+1}) - α(x_i)` is
  non-negative, which is foundational for bounding the upper and lower sums.

  Because of this, multiplying the integrator `α` by a scalar `k` poses a strict
  analytical constraint: *`k` must be non-negative (`k ≥ 0`)*.
  If `k` were negative, `k * α` would become monotonically decreasing, violating
  the core `SourceHypotheses` of the integral.

  ## Contents of this Section
  1. **Helper Lemmas**: Proofs that upper, lower, and tagged sums scale exactly
     by `k`. Furthermore, we prove that `SourceHypotheses` is preserved under
     multiplication by `k ≥ 0`.

  2. **Limit Theorems**: Proofs that the Darboux upper/lower limits and the
     tagged sum limits converge to `k * L`.

  3. **Main Theorems**:
     - `rsIntegrable_integrator_const_mul`: Given `f` is integrable w.r.t `α`,
       it is also integrable w.r.t `k * α`.
     - `rsIntegral_integrator_const_mul_eq`: The formal equality
       evaluating the integral as `k * ∫ f dα`.

  These theorems are essential for defining the expectation of probability
  distributions, as scaling the CDF by probability weights `p_i ≥ 0` natively
  satisfies this non-negative scalar requirement.
-/

end integrator_scalar_multiply
