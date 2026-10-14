-- Prove2me | Theorems.Thm_CondPortOT_SingUninf_ball_repr
-- name    : CondPortOT.SingUninf.ball_repr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:15.877658+00:00
-- url     : https://prove2.me/theorems/9920deb9-b99d-4fe2-8778-21a8a0001b6e
-- title:
--   p. 40 (= (24), p. 47) — 𝔹_ρ consists of the averages N⁻¹Σπᵢ with N⁻¹Σ E_πᵢ[𝔻(·, (x̂ᵢ, ŷᵢ))] ≤ ρ
-- statement:
--   Let $\mathcal X$, $\mathcal Y$ be Polish spaces with Borel $\sigma$-algebras, and let $\mathbb D_{\mathcal X}$, $\mathbb D_{\mathcal Y}$ be continuous real-valued ground costs, with $\mathbb D=\mathbb D_{\mathcal X}+\mathbb D_{\mathcal Y}$ on $\mathcal X\times\mathcal Y$. Let $N\ge1$, samples $(\widehat x_i,\widehat y_i)$, $i\in[N]$, with empirical measure $\widehat{\mathbb P}$, and $\rho\ge0$. Then a probability measure $\mathbb Q$ on $\mathcal X\times\mathcal Y$ lies in the optimal transport ball $\mathbb B_\rho$ if and only if there are probability measures $\pi_1,\dots,\pi_N$ on $\mathcal X\times\mathcal Y$ with
--
--   $$\mathbb Q=\frac1N\sum_{i\in[N]}\pi_i\qquad\text{and}\qquad\frac1N\sum_{i\in[N]}\int_{\mathcal X\times\mathcal Y}\big[\mathbb D_{\mathcal X}(x,\widehat x_i)+\mathbb D_{\mathcal Y}(y,\widehat y_i)\big]\,\pi_i(dx\times dy)\le\rho.$$
--
--   This decomposition, which splits a transport plan to the empirical measure into one conditional law per sample, is the representation of $\mathbb B_\rho$ from which all proofs of the paper start.
--
--   **Formalization Note** The integrand is $\max(\mathbb D,0)$ as a $[0,\infty]$-valued function and the integral is the lower Lebesgue integral. The forward direction needs an optimal coupling: the transport cost is defined as an infimum, and its attainment for a continuous (hence lower semicontinuous) cost on Polish spaces is the existence theorem the paper cites on p. 8; this is why the spaces are Polish. Repeated samples are allowed.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 40, proof of Proposition 3.1, first display (the same set as display (24), p. 47)

import Mathlib
import Definitions.Def_CondPortOT_SingUninf_Setting

open MeasureTheory

namespace CondPortOT.SingUninf

theorem ball_repr {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ)
    (hDX : Continuous (fun p : X × X => DX p.1 p.2)) (hDY : Continuous (fun p : Y × Y => DY p.1 p.2))
    {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Q : Measure (X × Y)) [IsProbabilityMeasure Q] :
    InBall DX DY xh yh ρ Q ↔
      ∃ π : Fin N → Measure (X × Y), (∀ i, IsProbabilityMeasure (π i)) ∧
        Q = (N : ENNReal)⁻¹ • ∑ i, π i ∧
        (N : ENNReal)⁻¹ * ∑ i, ∫⁻ z, groundCost DX DY z (xh i, yh i) ∂(π i) ≤ ENNReal.ofReal ρ := by sorry

end CondPortOT.SingUninf
