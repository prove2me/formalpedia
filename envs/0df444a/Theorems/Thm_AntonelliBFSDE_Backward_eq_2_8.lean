-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_eq_2_8
-- name    : AntonelliBFSDE.Backward.eq_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:22:13.59598+00:00
-- url     : https://prove2.me/theorems/708701e2-304b-41c7-9f61-43f8c2ca91a5
-- title:
--   (2.8) — $E\int_0^T|G^{(n)}(U)_t-G^{(n)}(V)_t|dA_t\le k^nE\int_0^TA_{t-}^{(n-)}|U_t-V_t|dA_t$
-- statement:
--   Under the assumptions of (2.7) — usual hypotheses, hypotheses 1–4, $A$ nondecreasing, $U,V\in L^1(\mu)$, and chains of Picard iterates $G^{(n)}(U)$, $G^{(n)}(V)$ — for every $n\ge1$,
--   $$E\Big(\int_0^T|G^{(n)}(U)_t-G^{(n)}(V)_t|\,dA_t\Big)\le k^n\,E\Big(\int_0^T A_{t-}^{(n-)}\,|U_t-V_t|\,dA_t\Big),$$
--   where $A^{(n-)}_{t-}$ is the left limit at $t$ of the iterated integral $A^{(n-)}$ and the integrals are over $(0,T]$.
--
--   Combined with $A^{(n-)}\le A^n/n!$ this gives the contraction estimate for $G^{(n)}$.
--
--   **Formalization Note** Both sides are lower integrals in $[0,\infty]$. The reduction to nondecreasing $A$ is as in (2.7); $U,V$ range over all of $L^1(\mu)$, as on the page.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 781, (2.8), proved on pp. 781–783

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- (2.8), proof of Theorem 2.4, p. 781 (`A` nondecreasing, any `U, V ∈ L¹(μ)`): for chains of
Picard iterates and every `n ≥ 1`,
`E(∫_0^T |G^{(n)}(U)_t - G^{(n)}(V)_t| dA_t) ≤ k^n E(∫_0^T A_{t-}^{(n-)} |U_t - V_t| dA_t)`. -/
theorem eq_2_8 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (hUH : UsualHypotheses 𝓕 P)
    (T β : ℝ≥0) (hT : 0 < T) (hβ : 0 < β) (I : BVIntegrator 𝓕 T β)
    (hA_incr : ∀ t ω, I.Aneg t ω = 0)
    (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ) (k : ℝ) (hyp : Hypotheses 𝓕 P I g Y k)
    (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1 P I U) (hV : MemL1 P I V)
    (Uᵢ Vᵢ : ℕ → ℝ≥0 → Ω → ℝ) (hU₀ : Uᵢ 0 = U) (hV₀ : Vᵢ 0 = V)
    (hUᵢ : ∀ j, IsGVersion 𝓕 P I g Y (Uᵢ j) (Uᵢ (j + 1)))
    (hVᵢ : ∀ j, IsGVersion 𝓕 P I g Y (Vᵢ j) (Vᵢ (j + 1)))
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ω, I.absLIntegral (fun s ω => Uᵢ n s ω - Vᵢ n s ω) 0 T ω ∂P ≤
      ENNReal.ofReal (k ^ n) *
        ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T,
          ENNReal.ofReal (Function.leftLim (iterIntMinus (fun r => I.A r ω) n) s.toNNReal) *
            ‖U s.toNNReal ω - V s.toNNReal ω‖ₑ ∂I.posMeasure ω ∂P := by sorry

end AntonelliBFSDE.Backward
