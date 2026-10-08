-- Prove2me | Theorems.Thm_AntonelliBFSDE_NonsingularExample_closed_form_V
-- name    : AntonelliBFSDE.NonsingularExample.closed_form_V
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:20.771795+00:00
-- url     : https://prove2.me/theorems/8d27ec11-79be-4c5b-9d34-11b6b67cc843
-- title:
--   Example 2 — closed form of V
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a complete, right-continuous filtration $(\mathcal F_t)_{0\le t\le T}$. Let $J_0$ be $\mathcal F_0$-measurable, integrable and strictly positive almost surely. Let $Y$ be $\mathcal F_T$-measurable, bounded and strictly positive almost surely. A solution $(U,V)$ belongs to $L^1(dt\otimes dP)^2$ and satisfies $U_t=J_0+\int_0^t V_s\,ds$ and $V_t=\mathbb E[\int_t^T U_s\,ds+Y\mid\mathcal F_t]$ in that space. Set $U_T=J_0+\int_0^T V_s\,ds$, $M_t=\mathbb E[U_T\mid\mathcal F_t]$, and $Y_t^{\mathrm c}=\mathbb E[Y\mid\mathcal F_t]$. For any $T>0$, and for jointly measurable versions $M,Y^{\mathrm c}$, the backward component satisfies, in $L^1(dt\otimes dP)$,
--
--   $$
--   V_t=M_t\sin(T-t)+Y_t^{\mathrm c}\cos(T-t).
--   $$
--
--   This explicit relation feeds the forward equation (3.10).
--
--   **Formalization Note** Equality is the vanishing $L^1(dt\otimes dP)$ norm of the difference. Both conditional-expectation processes are specified as versions, with their arguments integrable under the solution assumptions.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 792, Example 2, display after (3.12)

import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, p. 792: the sine-cosine form of the backward component. -/
theorem closed_form_V {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V M Yc : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P) (hT : 0 < T)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hYbounded : ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v) (fun u _ => u) Y U V)
    (hM : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => UT T J₀ V) M)
    (hYc : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => Y) Yc) :
    AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => V t ω -
      (M t ω * Real.sin ((T : ℝ) - (t : ℝ)) +
       Yc t ω * Real.cos ((T : ℝ) - (t : ℝ)))) = 0 := by sorry

end AntonelliBFSDE.NonsingularExample
