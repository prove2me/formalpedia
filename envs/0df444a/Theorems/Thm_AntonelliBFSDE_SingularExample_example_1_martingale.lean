-- Prove2me | Theorems.Thm_AntonelliBFSDE_SingularExample_example_1_martingale
-- name    : AntonelliBFSDE.SingularExample.example_1_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:24.700515+00:00
-- url     : https://prove2.me/theorems/b41ed4cc-1513-48f7-a793-4888bb1e49d9
-- title:
--   Example 1 — the sum of a linear-system solution is a martingale
-- statement:
--   Let $(U,V)$ solve the linear system (3.8)–(3.9) on $[0,T]$ under the assumptions of Example 1. There is a jointly measurable adapted process $N$ such that, for each $t\le T$,
--
--   $$
--   N_t=J_0+E_P\!\left[\int_0^T(U_s+V_s)\,ds+Y\mid\mathcal F_t\right]
--   $$
--
--   almost surely; $N$ is an integrable martingale on $[0,T]$; and $U+V=N$ in $L^1(dt\otimes P)$. This identifies the constant mean used in the next step.
--
--   **Formalization Note** A martingale means $N_s=E_P[N_t\mid\mathcal F_s]$ almost surely whenever $s\le t\le T$, with each $N_t$ integrable and $\mathcal F_t$-measurable. Equality with $U+V$ is $dt\otimes P$-almost everywhere, matching the paper's $L^1$ solution notion.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 791, Example 1, display after (3.9), https://doi.org/10.1214/aoap/1177005363

import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- Example 1, p. 791: adding (3.8) and (3.9) gives a martingale.
Equality with `U + V` is in `L¹(dt ⊗ P)`; the martingale law is for
every `s ≤ t ≤ T` up to `P`-almost-sure equality. -/
theorem example_1_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (hT : 0 < T)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYint : Integrable Y P)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V) :
    ∃ N : ℝ≥0 → Ω → ℝ,
      Measurable (Function.uncurry N) ∧
      (∀ t ≤ T, Integrable (N t) P ∧ StronglyMeasurable[𝓕 t] (N t) ∧
        N t =ᵐ[P] (fun ω => J₀ ω + P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] ω)) ∧
      (∀ s ≤ T, ∀ t ≤ T, s ≤ t → N s =ᵐ[P] P[N t | 𝓕 s]) ∧
      L1NormDt P T (fun t ω => U t ω + V t ω - N t ω) = 0 := by sorry

end AntonelliBFSDE.SingularExample
