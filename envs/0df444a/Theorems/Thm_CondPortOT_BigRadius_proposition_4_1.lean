-- Prove2me | Theorems.Thm_CondPortOT_BigRadius_proposition_4_1
-- name    : CondPortOT.BigRadius.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:39.621643+00:00
-- url     : https://prove2.me/theorems/2298dad1-c3cd-4210-bde4-87d2dbe8979b
-- title:
--   Proposition 4.1 — ρ_max(x₀, γ) = N⁻¹ Σ_{i∈ℐ₁} dᵢ
-- statement:
--   Let $\gamma>0$, let Assumption 2.4 hold, and let the boundary $\partial\mathcal N_\gamma(x_0)$ be regular in the sense of `BoundaryRegular` (nonempty, the exit cost of each sample inside the fiber equals its boundary distance $d_i$, and $d_i=\kappa_i$ outside). Then the minimal transport budget needed to empty the fiber,
--   $$\rho_{\max}(x_0,\gamma)=\inf\big\{\mathbb W(\mathbb Q,\hat{\mathbb P}):\mathbb Q\in\mathcal M(\mathcal X\times\mathcal Y),\ \mathbb Q(X\in\mathcal N_\gamma(x_0))=0\big\},$$
--   is given in closed form by
--   $$\rho_{\max}(x_0,\gamma)=\frac1N\sum_{i\in\mathcal I_1}d_i,$$
--   where $\mathcal I_1=\{i\in[N]:\hat x_i\in\mathcal N_\gamma(x_0)\}$ and $d_i=\min_{x\in\partial\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\hat x_i)$.
--
--   Each sample inside the fiber must be carried to the boundary and just beyond it, at cost $d_i/N$; samples outside stay put. The threshold separates the regime of Proposition 4.2 ($\rho>\rho_{\max}$) from that of Proposition 4.3 ($\rho<\rho_{\max}$).
--
--   **Formalization Note** The hypothesis `BoundaryRegular` is an addition to the paper. The paper's proof (pp. 45–46) uses $\inf_{x\notin\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\hat x_i)=d_i$ for $i\in\mathcal I_1$, which does not follow from Assumption 2.4 for a general continuous cost; it holds when $\mathbb D_{\mathcal X}$ is a norm distance. The predicate only concerns $\mathbb D_{\mathcal X}$ and the samples. $\rho_{\max}$ is valued in $[0,\infty]$; the right side is the nonnegative real $N^{-1}\sum_{\mathcal I_1}d_i$ embedded there.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 18, Proposition 4.1 (proof pp. 45–46)

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.BigRadius

theorem proposition_4_1 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : Assumption24 DX DY x0 γ xh)
    (hH2 : BoundaryRegular DX x0 γ xh) :
    rhoMax DX DY xh yh x0 γ =
      ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i ∈ I1 DX x0 γ xh, bdDist DX x0 γ xh i) := by sorry

end CondPortOT.BigRadius
