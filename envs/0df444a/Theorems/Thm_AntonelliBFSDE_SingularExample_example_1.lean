-- Prove2me | Theorems.Thm_AntonelliBFSDE_SingularExample_example_1
-- name    : AntonelliBFSDE.SingularExample.example_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:18.577655+00:00
-- url     : https://prove2.me/theorems/15acf65a-2fa1-4e0f-8593-0403e1bc7d77
-- title:
--   Example 1 — no solution when T ≥ 1
-- statement:
--   On a complete, right-continuous filtered probability space, let $J_0$ be $\mathcal F_0$-measurable, integrable and strictly positive almost surely, and let $Y$ be $\mathcal F_T$-measurable, integrable and strictly positive almost surely. If $T\ge1$, there is no pair $(U,V)\in L^1(dt\otimes P)^2$ solving
--
--   $$
--   U_t=J_0+\int_0^t(U_s+|V_s|)\,ds,\qquad
--   V_t=E_P\!\left[\int_t^T(U_s+V_s)\,ds+Y\mid\mathcal F_t\right].
--   $$
--
--   The solution class is that of $L^1(dt\otimes P)$: a solution is a pair of adapted processes in $L^1(dt\otimes P)$ satisfying both equations almost surely at each $t\le T$, and every $L^1$-class solution has such a representative. This example shows that the smallness condition $kT<1$ in the preceding existence theorem cannot simply be removed, even when the coefficients have Lipschitz constant $k=1$.
--
--   **Formalization Note** The source says “positive” and concludes nonexistence for $T\ge1$; positivity is read strictly almost surely, since $J_0=Y=0$ would admit the zero solution. The integrability of $J_0$ specializes §3's standing assumption $E\int_0^T|J_t|\,dD_t<\infty$ for $J_t=J_0$ and $D_t=t$. A jointly measurable conditional-expectation version and integrability of its argument are explicit. Real time is encoded by $\mathbb R_{\ge0}$, and the integrals are over $(s,t]$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 790–791, Example 1, (3.6)–(3.9), https://doi.org/10.1214/aoap/1177005363

import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- Example 1, pp. 790–791: the linear system (3.6)–(3.7) has no
`L¹(dt ⊗ P)` solution at any horizon `T ≥ 1`. "Positive" is read strictly. -/
theorem example_1 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (hT : 1 ≤ T)
    (J₀ Y : Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYint : Integrable Y P)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω) :
    ¬ ∃ U V : ℝ≥0 → Ω → ℝ,
      IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|)
        (fun u v => u + v) Y U V := by sorry

end AntonelliBFSDE.SingularExample
