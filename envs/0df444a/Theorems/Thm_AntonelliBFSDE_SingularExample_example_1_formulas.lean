-- Prove2me | Theorems.Thm_AntonelliBFSDE_SingularExample_example_1_formulas
-- name    : AntonelliBFSDE.SingularExample.example_1_formulas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:00.371643+00:00
-- url     : https://prove2.me/theorems/bb313ad2-7169-4c5f-bba4-a2ef598c030e
-- title:
--   Example 1 — representations of U and V
-- statement:
--   Suppose $(U,V)$ solves Antonelli's system (3.6)–(3.7) on a positive horizon $T$, with $J_0>0$ and $Y>0$ almost surely and the filtered-space and integrability assumptions of Example 1. Then the two processes can be expressed in terms of each other:
--
--   $$
--   U_t=e^t\left(J_0+\int_0^t e^{-s}|V_s|\,ds\right),\qquad
--   V_t=E_P\!\left[e^{T-t}Y+\int_t^T e^{s-t}U_s\,ds\mid\mathcal F_t\right].
--   $$
--
--   The identities hold $dt\otimes P$-almost everywhere. The random variable inside the second conditional expectation is integrable for each $t\le T$. These formulas isolate the positivity mechanism used in Example 1.
--
--   **Formalization Note** The source writes pointwise process formulas; the solution itself is an $L^1(dt\otimes P)$ equivalence class, so the formal statements assert zero $L^1$ residual and a jointly measurable conditional-expectation version. The paper's “positive” is read as strictly positive almost surely; its §3 integrability condition on the constant input process $J_t=J_0$ is stated as $J_0\in L^1(P)$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 790, Example 1, two displays after (3.7), https://doi.org/10.1214/aoap/1177005363

import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- The two displayed representations in Example 1, p. 790, read as
`dt ⊗ P`-almost-everywhere identities. -/
theorem example_1_formulas {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (hT : 0 < T)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYint : Integrable Y P)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|)
      (fun u v => u + v) Y U V) :
    L1NormDt P T (fun t ω => U t ω -
      Real.exp (t : ℝ) * (J₀ ω +
        ∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
          Real.exp (-s) * |V s.toNNReal ω|)) = 0 ∧
    (∀ t ≤ T, Integrable
      (fun ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
        ∫ s in Set.Ioc (t : ℝ) (T : ℝ),
          Real.exp (s - (t : ℝ)) * U s.toNNReal ω) P) ∧
    ∃ W : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T
        (fun t ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
          ∫ s in Set.Ioc (t : ℝ) (T : ℝ),
            Real.exp (s - (t : ℝ)) * U s.toNNReal ω) W ∧
      L1NormDt P T (fun t ω => W t ω - V t ω) = 0 := by sorry

end AntonelliBFSDE.SingularExample
