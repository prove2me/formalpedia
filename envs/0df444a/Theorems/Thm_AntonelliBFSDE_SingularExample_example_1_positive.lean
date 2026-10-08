-- Prove2me | Theorems.Thm_AntonelliBFSDE_SingularExample_example_1_positive
-- name    : AntonelliBFSDE.SingularExample.example_1_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:36.097634+00:00
-- url     : https://prove2.me/theorems/15837a8f-eef5-437d-aa62-21da77cd7257
-- title:
--   Example 1 — positivity and the linear system (3.8)–(3.9)
-- statement:
--   Let $(U,V)$ solve (3.6)–(3.7) under the positive and integrable data of Example 1. Then $U_t>0$ and $V_t>0$ for $dt\otimes P$-almost every $(t,\omega)$. Consequently $|V_t|=V_t$ almost everywhere, and the same pair solves the linear system
--
--   $$
--   U_t=J_0+\int_0^t(U_s+V_s)\,ds,\qquad
--   V_t=E_P\!\left[\int_t^T(U_s+V_s)\,ds+Y\mid\mathcal F_t\right].
--   $$
--
--   This is the passage from (3.6)–(3.7) to (3.8)–(3.9) in the example.
--
--   **Formalization Note** Positivity is expressed for almost every time and almost every sample point. The source's “positive” is read strictly almost surely; $J_0\in L^1(P)$ is the specialization of §3's standing input-integrability assumption.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 791, Example 1, (3.8)–(3.9), https://doi.org/10.1214/aoap/1177005363

import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- Example 1, p. 791: the hypothetical solution is positive almost
everywhere and hence also solves the system (3.8)–(3.9). -/
theorem example_1_positive {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      ∀ᵐ ω ∂P, 0 < U r.toNNReal ω ∧ 0 < V r.toNNReal ω) ∧
    IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V := by sorry

end AntonelliBFSDE.SingularExample
