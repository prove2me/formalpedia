-- Prove2me | solution 1 for indicatorConstIntegral_def_6_2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:41:32.627358+00:00
-- url     : https://prove2.me/submissions/96f7c5fa-aa47-4801-b397-4d7550643574

import Theorems.Thm_def62_eq_some_iff
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic


/-

  # Example 6.1.2
Lebesgue Integral of a Single Indicator Function
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators

/-
\textbf{Example 6.1.2 (Lebesgue Integral of a Single Indicator Function)} \\
Suppose $B$ is a measurable set. By Theorem 4.1, the indicator function $1_B$ is measurable. It takes two values and can be expressed as
\[
1_B(\omega)=1\cdot 1_B(\omega)+0\cdot 1_{B^c}(\omega).
\]
The Lebesgue integral $\int 1_B\, d\mu$ equals $1\cdot \mu(B)+0\cdot \mu(B^c)=\mu(B)$, where the second term $0\cdot \mu(B^c)$ is $0$ by the convention of $0\cdot x=0$.
-/


private theorem source_const_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : EReal) (B : Set Ω) (hB : MeasurableSet B) (hc : c = 0) :
    def_6_2 μ ((SimpleFunc.const Ω c).restrict B) = some (c * (μ B : EReal)) := by
  simp_all [def62_eq_some_iff, SimpleFunc.restrict]
  simp +decide [ simpleFunctionIntegralValue, simpleFunctionIntegralTerm ];
  refine' ⟨ _, _ ⟩;
  · simp [ simpleFunctionIntegralDefined,
      simpleFunctionHasPosInf, simpleFunctionHasNegInf ];
    unfold simpleFunctionIntegralTerm;
    intro a a_1 a_2
    subst hc
    simp_all only [SimpleFunc.coe_zero, zero_mul, EReal.zero_ne_top];
  · rw [ Finset.sum_eq_zero ] ;
    intro x a
    subst hc
    simp_all only [SimpleFunc.mem_range,
      SimpleFunc.coe_zero, Set.mem_range, Pi.zero_apply, exists_const_iff]
    obtain ⟨left, right⟩ := a
    subst right
    simp_all only [zero_mul];

private theorem source_const_integral_nonzero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : EReal) (B : Set Ω) (hB : MeasurableSet B) (hc : c ≠ 0) :
    def_6_2 μ ((SimpleFunc.const Ω c).restrict B) = some (c * (μ B : EReal)) := by
  simp_all [def62_eq_some_iff, SimpleFunc.restrict]
  refine' ⟨ _, _ ⟩;
  · refine' fun h => _;
    obtain ⟨ ⟨ x, hx₁, hx₂ ⟩, ⟨ y, hy₁, hy₂ ⟩ ⟩ := h;
    simp_all [ SimpleFunc.range, simpleFunctionIntegralTerm ];
    rcases hx₁ with ⟨ x, rfl ⟩ ; rcases hy₁ with ⟨ y, rfl ⟩ ;
    by_cases hx : x ∈ B <;>
    by_cases hy : y ∈ B <;>
    simp_all [ Set.indicator ]
  · rw [ simpleFunctionIntegralValue ];
    rw [ Finset.sum_eq_single c ] <;>
    simp [ hc, simpleFunctionIntegralTerm ];
    · congr ; ext x ; by_cases hx : x ∈ B <;> simp  [hx];
      exact Ne.symm hc;
    · intro a ha;
      contrapose! ha;
      simp_all only [ne_eq, Set.indicator_of_mem, Function.const_apply];
    · intro h;
      rw [ show ( B.indicator ( Function.const Ω c ) ) ⁻¹' { c } = ∅ by ext x; specialize h x; aesop ] ;
      simp

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : EReal) (B : Set Ω) (hB : MeasurableSet B) :
    def_6_2 μ ((SimpleFunc.const Ω c).restrict B) = some (c * (μ B : EReal)) := by
  by_cases hc : c = 0
  · exact source_const_integral_zero μ c B hB hc
  · exact source_const_integral_nonzero μ c B hB hc
