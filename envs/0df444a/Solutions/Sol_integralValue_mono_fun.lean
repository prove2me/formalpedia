-- Prove2me | solution 1 for integralValue_mono_fun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:19:58.790382+00:00
-- url     : https://prove2.me/submissions/b4887817-a48c-44d5-8a3e-3a7e53871ae3

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
import Theorems.Thm_integralValue_map


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


theorem solution (μ : Measure Ω) {f g : SimpleFunc Ω EReal} (hfg : f ≤ g) :
    simpleFunctionIntegralValue μ f ≤ simpleFunctionIntegralValue μ g := by
  classical
  calc
    simpleFunctionIntegralValue μ f
        = simpleFunctionIntegralValue μ ((f.pair g).map Prod.fst) := by
            simp
    _ = ∑ x ∈ (f.pair g).range, x.1 * (μ (f.pair g ⁻¹' {x}) : EReal) := by
          rw [integralValue_map (μ := μ) (g := Prod.fst)]
    _ ≤ ∑ x ∈ (f.pair g).range, x.2 * (μ (f.pair g ⁻¹' {x}) : EReal) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hxle : x.1 ≤ x.2 := by
            rcases SimpleFunc.mem_range.1 hx with ⟨ω, rfl⟩
            exact hfg ω
          have hμnonneg : 0 ≤ (μ (f.pair g ⁻¹' {x}) : EReal) := by
            positivity
          exact mul_le_mul_of_nonneg_right hxle hμnonneg
    _ = simpleFunctionIntegralValue μ ((f.pair g).map Prod.snd) := by
          rw [integralValue_map (μ := μ) (g := Prod.snd)]
    _ = simpleFunctionIntegralValue μ g := by
          simp
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
