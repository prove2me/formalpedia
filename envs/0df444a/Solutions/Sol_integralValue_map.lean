-- Prove2me | solution 1 for integralValue_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:34:51.986379+00:00
-- url     : https://prove2.me/submissions/f1ae07da-ee01-420c-afdc-9d905ebfe931

import Theorems.Thm_ereal_coe_finset_sum__138bdd
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic


/-

  # Lebesgue integral of simple function

-/

/-
\begin{defbox}{6.2}
The \textit{Lebesgue integral} of a simple function $X$ expressed as in (6.1) is defined by
\begin{equation}
\int X\, d\mu \triangleq \sum_{i=1}^{n} a_i \mu(A_i),
\tag{6.2}
\end{equation}
unless the summation contains both $\infty$ and $-\infty$, in which case the integral is not defined.
\end{defbox}
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]


/-- Original distributivity calculation over nonnegative EReal measure values. -/
private theorem source_ereal_measure_sum_distrib
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type*} (g : β → EReal) (f : SimpleFunc Ω β)
    (a : Ω) (s : Finset β) :
    g (f a) * ∑ y ∈ s, ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
      ∑ y ∈ s, g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert y s hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy]
      have hy_nonneg : 0 ≤ ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
        positivity
      have hs_nonneg : 0 ≤ ∑ z ∈ s, ((μ (f ⁻¹' {z}) : ENNReal) : EReal) := by
        positivity
      rw [EReal.left_distrib_of_nonneg hy_nonneg hs_nonneg, ih]

theorem solution (μ : Measure Ω) {β : Type*}
    (g : β → EReal) (f : SimpleFunc Ω β) :
    simpleFunctionIntegralValue μ (f.map g) =
      ∑ x ∈ f.range, g x * (μ (f ⁻¹' {x}) : EReal) := by
  classical
  simp only [simpleFunctionIntegralValue, SimpleFunc.range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases SimpleFunc.mem_range.1 hb with ⟨a, rfl⟩
  simp only [simpleFunctionIntegralTerm]
  rw [SimpleFunc.map_preimage_singleton]
  have hsum :
      ((μ (f ⁻¹' ↑({b ∈ f.range | g b = g (f a)})) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)), ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    rw [← f.sum_measure_preimage_singleton (s := f.range.filter fun y => g y = g (f a)),
      ereal_coe_finset_sum]
  let s : Finset β := f.range.filter fun y => g y = g (f a)
  have hdist := source_ereal_measure_sum_distrib μ g f a s
  have hsum_mul :
      g (f a) * (μ (f ⁻¹' ↑({b ∈ f.range | g b = g (f a)})) : EReal) =
        g (f a) * ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    exact congrArg (fun t : EReal => g (f a) * t) hsum
  have hdist' :
      g (f a) * ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    simpa [s] using hdist
  have hpointwise :
      ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g y * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [(Finset.mem_filter.1 hy).2]
  simpa using hsum_mul.trans (hdist'.trans hpointwise)
---------------------------
-- Connection to Mathlib
---------------------------

/-
An `ENNReal`-valued simple function has no negative-infinite integral term.
-/

/-
Definition 6.2 is defined for every nonnegative simple function.
-/

/-
The textbook value agrees with Mathlib's `SimpleFunc.lintegral`.
-/

/-
Definition 6.2 agrees with Mathlib's simple-function lower integral.
-/
