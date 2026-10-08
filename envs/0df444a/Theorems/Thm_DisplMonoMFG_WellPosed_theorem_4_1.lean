-- Prove2me | Theorems.Thm_DisplMonoMFG_WellPosed_theorem_4_1
-- name    : DisplMonoMFG.WellPosed.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:44.506576+00:00
-- url     : https://prove2.me/theorems/d964a314-a575-4dec-983e-a5a5594d5e65
-- title:
--   Theorem 4.1 — displacement monotonicity propagates along classical solutions of the master equation
-- statement:
--   Let $T>0$ and $\beta\ge0$. Let $G$ satisfy Assumption 3.1, let $H$ satisfy Assumption 3.2(i) and (iv), and let Assumption 3.5 hold: $G$ satisfies (2.16) and $H$ satisfies (3.2). Let $V$ be a classical solution of the master equation (1.1) on $[0,T]$. Assume further that
--   $$
--   V(t,\cdot,\cdot),\ \partial_xV(t,\cdot,\cdot),\ \partial_{xx}V(t,\cdot,\cdot)\in\mathcal C^2(\mathbb R^d\times\mathcal P_2),\qquad\partial_\mu V(t,\cdot,\cdot,\cdot),\ \partial_{x\mu}V(t,\cdot,\cdot,\cdot)\in\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^d),
--   $$
--   and that all their derivatives in the state and measure variables are continuous in time and uniformly bounded. Then, for every $t\in[0,T]$, $V(t,\cdot,\cdot)$ is displacement monotone:
--   $$
--   (d_xd)_\xi V(t,\cdot,\cdot)(\eta,\eta)\ge0\qquad\text{for all }\xi,\eta\in\mathbb L^2.
--   $$
--
--   The paper calls this "the heart of our analysis". Displacement monotonicity is preserved backward in time, and it yields the a priori Lipschitz estimates in $\mu$ that extend local solutions to global ones.
--
--   **Formalization Note** Assumptions 3.2(ii) and (iii) are not assumed, as on the page. "Uniformly bounded" means one bound over $t\in[0,T]$ and all state and measure arguments.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), Theorem 4.1, p. 2195

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Master

open MeasureTheory

namespace DisplMonoMFG.WellPosed

/-- Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022), Theorem 4.1, p. 2195 (PDF p. 18):
let Assumptions 3.1, 3.2(i), (iv) and 3.5 hold, and let `V` be a classical solution of the master
equation (1.1) on `[0, T]` such that `V(t,·,·), ∂_x V(t,·,·), ∂_xx V(t,·,·) ∈ 𝒞²(ℝ^d × 𝒫₂)`,
`∂_μ V(t,·,·,·), ∂_xμ V(t,·,·,·) ∈ 𝒞²(ℝ^d × 𝒫₂ × ℝ^d)`, all their state/measure derivatives
being continuous in time and uniformly bounded. Then `V(t,·,·)` satisfies (2.16) for all
`t ∈ [0, T]`. Assumptions 3.2(ii), (iii) are not assumed. -/
theorem theorem_4_1 {d : ℕ} (T β : ℝ) (hT : 0 < T) (hβ : 0 ≤ β)
    (H : E d → P2 d → E d → ℝ) (G : E d → P2 d → ℝ)
    (wH : C2W d (E d × E d) ℝ) (wG : C2W d (E d) ℝ)
    (hG : Assm31 G wG) (LH : ℝ → ℝ) (hHi : Assm32i H wH LH) (hHiv : Assm32iv H wH LH)
    (hM : Assm35 wG wH)
    (V Vt : ℝ → E d → P2 d → ℝ) (w : ℝ → C2W d (E d) ℝ)
    (hV : IsClassicalSol β 0 T H G V Vt w) (hR : HighReg (Set.Icc 0 T) V w) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, DisplMono (w t) := by sorry

end DisplMonoMFG.WellPosed
