-- Prove2me | Theorems.Thm_CondPortOT_NullFiber_ball_repr
-- name    : CondPortOT.NullFiber.ball_repr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:09.757307+00:00
-- url     : https://prove2.me/theorems/454633ca-bc86-4790-92a0-6ccea28129bc
-- title:
--   (24), p. 47 — 𝔹_ρ consists of the averages N⁻¹Σπᵢ of probability measures with N⁻¹ΣE_πᵢ[𝔻(·, (x̂ᵢ, ŷᵢ))] ≤ ρ
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $(\hat x_i,\hat y_i)_{i\in[N]}$ samples with $N\ge1$, and let the costs $\mathbb D_{\mathcal X},\mathbb D_{\mathcal Y}$ satisfy Assumption 2.4 (for some $x_0$, $\gamma$). Let $\rho\ge0$ and let $\mathbb Q$ be a measure on $\mathcal X\times\mathcal Y$. Then $\mathbb Q\in\mathbb B_\rho$, i.e. $\mathbb Q$ is a probability measure with $\mathbb W(\mathbb Q,\widehat{\mathbb P})\le\rho$, if and only if $\mathbb Q$ is a probability measure and there are probability measures $\pi_1,\dots,\pi_N$ on $\mathcal X\times\mathcal Y$ such that
--
--   $$\mathbb Q=\frac1N\sum_{i\in[N]}\pi_i\qquad\text{and}\qquad \frac1N\sum_{i\in[N]}\mathbb E_{\pi_i}\big[\mathbb D_{\mathcal X}(X,\hat x_i)+\mathbb D_{\mathcal Y}(Y,\hat y_i)\big]\le\rho.$$
--
--   This is the representation of the ambiguity set from which the proofs of Propositions 4.2, 4.3 and Theorem 4.4 start: $\pi_i$ is the distribution to which the $i$-th sample is transported.
--
--   **Formalization Note** The inequality is exactly $\le\rho$, not $\le\rho+\delta$ for every $\delta>0$; the forward direction therefore needs an optimal coupling, which exists because the cost is continuous and the spaces are Polish (the paper cites Villani's Theorem 4.1 on p. 8). Expectations of the cost are lower Lebesgue integrals of the $[0,\infty]$-valued cost; the sum is scaled by $N^{-1}$ in $[0,\infty]$.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 47, display (24) in the proof of Proposition 4.3

import Mathlib
import Definitions.Def_CondPortOT_NullFiber_Setting

namespace CondPortOT.NullFiber

open MeasureTheory

theorem ball_repr {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hA : Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (Q : Measure (X × Y)) :
    CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ↔
      IsProbabilityMeasure Q ∧
        ∃ π : Fin N → Measure (X × Y), (∀ i, IsProbabilityMeasure (π i)) ∧
          Q = (N : ENNReal)⁻¹ • ∑ i, π i ∧
          (N : ENNReal)⁻¹ * ∑ i, ∫⁻ z, CondPortOT.SingUninf.groundCost DX DY z (xh i, yh i) ∂(π i) ≤
            ENNReal.ofReal ρ := by sorry

end CondPortOT.NullFiber
