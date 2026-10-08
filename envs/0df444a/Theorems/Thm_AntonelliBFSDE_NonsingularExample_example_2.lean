-- Prove2me | Theorems.Thm_AntonelliBFSDE_NonsingularExample_example_2
-- name    : AntonelliBFSDE.NonsingularExample.example_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:44.160987+00:00
-- url     : https://prove2.me/theorems/89b95d0d-4ea8-49d1-af7b-be7b722c0567
-- title:
--   Example 2 — no solution at T = π/2
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a complete, right-continuous filtration $(\mathcal F_t)_{0\le t\le T}$. Let $J_0$ be $\mathcal F_0$-measurable, integrable and strictly positive almost surely. Let $Y$ be $\mathcal F_T$-measurable, bounded and strictly positive almost surely. A solution $(U,V)$ belongs to $L^1(dt\otimes dP)^2$ and satisfies $U_t=J_0+\int_0^t V_s\,ds$ and $V_t=\mathbb E[\int_t^T U_s\,ds+Y\mid\mathcal F_t]$ in that space. Set $U_T=J_0+\int_0^T V_s\,ds$, $M_t=\mathbb E[U_T\mid\mathcal F_t]$, and $Y_t^{\mathrm c}=\mathbb E[Y\mid\mathcal F_t]$. When the horizon is $T=\pi/2$, there is no pair of integrable processes satisfying the coupled system:
--
--   $$
--   \nexists\,(U,V)\in L^1(dt\otimes dP)^2:\quad
--   U_t=J_0+\int_0^t V_s\,ds,\qquad
--   V_t=\mathbb E[\int_t^T U_s\,ds+Y\mid\mathcal F_t].
--   $$
--
--   This is the nonsingular counterexample: a finite Lipschitz constant alone does not ensure existence at every finite horizon.
--
--   **Formalization Note** The paper says that $U_T$ is no longer integrable and the system does not make sense at $T=\pi/2$. We state the resulting nonexistence of an $L^1$ solution. The paper calls $J_0,Y$ positive; strict positivity almost surely is required, because zero data admit the zero solution. Integrability of $J_0$ is the §3 standing assumption on $J$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 791–792, Example 2, (3.10)–(3.13) and concluding sentence

import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, pp. 791–792: nonexistence at the nonsingular critical horizon. -/
theorem example_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P) (hT : (T : ℝ) = Real.pi / 2)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hYbounded : ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C) :
    ¬ ∃ U V : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v) (fun u _ => u) Y U V := by sorry

end AntonelliBFSDE.NonsingularExample
