-- Prove2me | Theorems.Thm_CondPortOT_BigRadius_ball_repr
-- name    : CondPortOT.BigRadius.ball_repr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:38.871308+00:00
-- url     : https://prove2.me/theorems/2f05e4fb-088d-4731-b972-9caa3e1e83cc
-- title:
--   (24), p. 47 — 𝔹_ρ consists of the averages N⁻¹Σπᵢ with N⁻¹ΣE_πᵢ[𝔻(·, (x̂ᵢ, ŷᵢ))] ≤ ρ
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $(\hat x_i,\hat y_i)_{i\in[N]}$ data with $N\ge1$, $\hat{\mathbb P}$ the empirical distribution, and let the ground costs $\mathbb D_{\mathcal X},\mathbb D_{\mathcal Y}$ satisfy Assumption 2.4 (for some $x_0$ and $\gamma>0$). For $\rho\ge0$ and every probability measure $\mathbb Q$ on $\mathcal X\times\mathcal Y$, $\mathbb Q$ lies in the optimal transport ball $\mathbb B_\rho=\{\mathbb Q:\mathbb W(\mathbb Q,\hat{\mathbb P})\le\rho\}$ if and only if there are probability measures $\pi_1,\dots,\pi_N$ on $\mathcal X\times\mathcal Y$ with
--   $$\mathbb Q=\frac1N\sum_{i\in[N]}\pi_i,\qquad \frac1N\sum_{i\in[N]}\mathbb E_{\pi_i}\big[\mathbb D_{\mathcal X}(X,\hat x_i)+\mathbb D_{\mathcal Y}(Y,\hat y_i)\big]\le\rho .$$
--
--   This is display (24) of the paper: each $\pi_i$ is where the mass of the $i$-th sample is sent. Every argument of §4 about measures in $\mathbb B_\rho$ starts from it.
--
--   **Formalization Note** The expectations are lower Lebesgue integrals of the $[0,\infty]$-valued cost. The direction "$\mathbb Q\in\mathbb B_\rho\Rightarrow$ decomposition" requires the transport infimum to be attained (Villani, *Optimal Transport*, Theorem 4.1, cited by the paper on p. 8), which is why the spaces are Polish. Only Assumption 2.4(i) is relevant; the full assumption is carried as the paper's standing hypothesis.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 47, display (24) (proof of Proposition 4.3); also p. 40

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.BigRadius

theorem ball_repr {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Q : Measure (X × Y)) [IsProbabilityMeasure Q] :
    CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ↔
      ∃ π : Fin N → Measure (X × Y), (∀ i, IsProbabilityMeasure (π i)) ∧
        Q = (N : ENNReal)⁻¹ • ∑ i, π i ∧
        (N : ENNReal)⁻¹ * ∑ i, ∫⁻ z, CondPortOT.SingUninf.groundCost DX DY z (xh i, yh i) ∂(π i) ≤ ENNReal.ofReal ρ := by sorry

end CondPortOT.BigRadius
