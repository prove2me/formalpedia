-- Prove2me | solution 1 for ex_6_1_2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:28:22.888779+00:00
-- url     : https://prove2.me/submissions/f29512cc-0df7-48b6-a76e-ccf962a84a0f

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Theorems.Thm_def62_eq_some_iff
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


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (B : Set Ω)
    (hB : MeasurableSet B) :
    Measurable
        (((SimpleFunc.const Ω (1 : EReal)).restrict B : SimpleFunc Ω EReal) : Ω → EReal) ∧
      ∀ {x : EReal},
        def_6_2 μ ((SimpleFunc.const Ω (1 : EReal)).restrict B) = some x →
        x = (μ B : EReal) := by
  refine ⟨SimpleFunc.measurable ((SimpleFunc.const Ω 1).restrict B), ?_⟩
  · intro x hx
    have h_sum :
        (∑ y ∈ ((SimpleFunc.const Ω 1).restrict B).range,
            y * (μ (((SimpleFunc.const Ω 1).restrict B) ⁻¹' {y} : Set Ω) : EReal)) =
          (1 : EReal) * (μ B : EReal) := by
      simp  [SimpleFunc.restrict ];
      split_ifs ; simp_all [ SimpleFunc.range ];
      rw [ Finset.sum_eq_single 1 ] <;> simp +contextual [ Set.indicator ];
      · congr with x ; simp [ Set.indicator ];
      · intro h; simp [ Set.preimage, h ] ;
    convert h_sum using 1;
    · exact def62_eq_some_iff _ _ _ |>.1 hx |>.2.symm;
    · norm_num