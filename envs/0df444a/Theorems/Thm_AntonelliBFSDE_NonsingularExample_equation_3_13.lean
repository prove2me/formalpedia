-- Prove2me | Theorems.Thm_AntonelliBFSDE_NonsingularExample_equation_3_13
-- name    : AntonelliBFSDE.NonsingularExample.equation_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:00:51.758901+00:00
-- url     : https://prove2.me/theorems/d46417e6-db1e-4413-9713-b0780f400906
-- title:
--   Equation (3.13) — forward component in closed form
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a complete, right-continuous filtration $(\mathcal F_t)_{0\le t\le T}$. Let $J_0$ be $\mathcal F_0$-measurable, integrable and strictly positive almost surely. Let $Y$ be $\mathcal F_T$-measurable, bounded and strictly positive almost surely. A solution $(U,V)$ belongs to $L^1(dt\otimes dP)^2$ and satisfies $U_t=J_0+\int_0^t V_s\,ds$ and $V_t=\mathbb E[\int_t^T U_s\,ds+Y\mid\mathcal F_t]$ in that space. Set $U_T=J_0+\int_0^T V_s\,ds$, $M_t=\mathbb E[U_T\mid\mathcal F_t]$, and $Y_t^{\mathrm c}=\mathbb E[Y\mid\mathcal F_t]$. For any $T>0$, and for jointly measurable versions $M,Y^{\mathrm c}$, the forward component obeys, in $L^1(dt\otimes dP)$,
--
--   $$
--   U_t=J_0+\int_0^t M_s\sin(T-s)\,ds+\int_0^t Y_s^{\mathrm c}\cos(T-s)\,ds.
--   $$
--
--   The same formula at $t=T$ holds almost surely for the terminal value $U_T$ defined by the forward integral. Its terminal form is used in the mean identity.
--
--   **Formalization Note** The endpoint value is reconstructed from $V$; an arbitrary $L^1$ representative's value $U(T,\omega)$ is not used.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 792, Example 2, (3.13)

import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, (3.13), including the terminal identity using the forward integral. -/
theorem equation_3_13 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
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
    AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => U t ω -
      (J₀ ω + (∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
        M s.toNNReal ω * Real.sin ((T : ℝ) - s)) +
       (∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
        Yc s.toNNReal ω * Real.cos ((T : ℝ) - s)))) = 0 ∧
    (∀ᵐ ω ∂P, UT T J₀ V ω =
      J₀ ω + (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
        M s.toNNReal ω * Real.sin ((T : ℝ) - s)) +
      (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
        Yc s.toNNReal ω * Real.cos ((T : ℝ) - s))) := by sorry

end AntonelliBFSDE.NonsingularExample
