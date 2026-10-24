-- Prove2me | Theorems.Thm_CondPortOT_NullFiber_proposition_4_1
-- name    : CondPortOT.NullFiber.proposition_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:06.942521+00:00
-- url     : https://prove2.me/theorems/980c7caa-3193-444d-9851-b3ab90bf3c9c
-- title:
--   Proposition 4.1 — ρ_max(x₀, γ) = N⁻¹ Σ_{i∈ℐ₁} dᵢ
-- statement:
--   Let $\gamma>0$, let Assumption 2.4 hold, and let the boundary of $\mathcal N_\gamma(x_0)$ be regular in the sense of `BoundaryRegular` (it is nonempty, and leaving $\mathcal N_\gamma(x_0)$ from a sample $\hat x_i\in\mathcal N_\gamma(x_0)$ costs $d_i$ in the limit). Then the minimal transport budget needed to move all the mass of the empirical distribution out of the fiber is
--
--   $$\rho_{\max}(x_0,\gamma)=\frac1N\sum_{i\in\mathcal I_1}d_i,$$
--
--   where $\mathcal I_1=\{i\in[N]:\hat x_i\in\mathcal N_\gamma(x_0)\}$ and $d_i$ is the cost from $\hat x_i$ to the boundary $\partial\mathcal N_\gamma(x_0)$.
--
--   This closed form identifies the threshold that separates the informative regime $\rho<\rho_{\max}$ of Proposition 4.3 from the uninformative regime $\rho>\rho_{\max}$ of Proposition 4.2.
--
--   **Formalization Note** $\rho_{\max}$ is an infimum in $[0,\infty]$, compared with the real right-hand side through `ENNReal.ofReal`. The hypothesis `BoundaryRegular` is an addition to the page: without it the statement fails for a general continuous cost (the exit infimum can be smaller than $d_i$).
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 18, Proposition 4.1

import Mathlib
import Definitions.Def_CondPortOT_NullFiber_Setting

namespace CondPortOT.NullFiber

open MeasureTheory

theorem proposition_4_1 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ)
    (hA : Assumption24 DX DY x0 γ xh) (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh) :
    CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ =
      ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i ∈ CondPortOT.BigRadius.I1 DX x0 γ xh, CondPortOT.BigRadius.bdDist DX x0 γ xh i) := by sorry

end CondPortOT.NullFiber
