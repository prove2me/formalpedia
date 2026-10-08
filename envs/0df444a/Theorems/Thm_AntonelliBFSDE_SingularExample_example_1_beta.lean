-- Prove2me | Theorems.Thm_AntonelliBFSDE_SingularExample_example_1_beta
-- name    : AntonelliBFSDE.SingularExample.example_1_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:15.343889+00:00
-- url     : https://prove2.me/theorems/a4ecf12f-e441-4660-ac1f-e63df82fcb8b
-- title:
--   Example 1 — the constant mean satisfies β(1 − T) = E(J₀ + Y)
-- statement:
--   Let $(U,V)$ solve (3.8)–(3.9), and let $\beta$ be the mean of the martingale obtained by adding the two equations:
--
--   $$
--   \beta=E_P\!\left[J_0+\int_0^T(U_s+V_s)\,ds+Y\right].
--   $$
--
--   Then
--
--   $$
--   \beta(1-T)=E_P[J_0+Y]>0.
--   $$
--
--   This is the identity that rules out a solution at $T=1$ and, together with positivity, at larger horizons. The $\beta$ here denotes a martingale mean, not the bound on total variation used elsewhere in the paper.
--
--   **Formalization Note** $\beta$ is the displayed integral computed from the data rather than an arbitrary parameter. Strict positivity of $J_0,Y$ is explicit. The conditional-expectation arguments are required integrable by the solution concept, avoiding a default-value interpretation.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 791, Example 1, displays after (3.9), https://doi.org/10.1214/aoap/1177005363

import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- Example 1, p. 791: if `β` is the constant mean of the martingale
obtained by adding (3.8) and (3.9), then `β(1-T)=E(J₀+Y)>0`. -/
theorem example_1_beta {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      Integrable (fun ω => U r.toNNReal ω + V r.toNNReal ω) P ∧
      (∫ ω, U r.toNNReal ω + V r.toNNReal ω ∂P) =
        (∫ ω, J₀ ω + xiDt T (fun u v => u + v) Y U V 0 ω ∂P) ∧
      (∫ ω, U r.toNNReal ω + V r.toNNReal ω ∂P) =
        (∫ ω, J₀ ω ∂P) +
        (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ ω, U s.toNNReal ω + V s.toNNReal ω ∂P) +
        (∫ ω, Y ω ∂P)) ∧
    (∫ ω, J₀ ω + xiDt T (fun u v => u + v) Y U V 0 ω ∂P) *
      (1 - (T : ℝ)) = ∫ ω, J₀ ω + Y ω ∂P ∧
    0 < ∫ ω, J₀ ω + Y ω ∂P := by sorry

end AntonelliBFSDE.SingularExample
