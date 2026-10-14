-- Prove2me | Theorems.Thm_CondPortOT_FiberDual_ball_repr
-- name    : CondPortOT.FiberDual.ball_repr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:07.865986+00:00
-- url     : https://prove2.me/theorems/1658671d-32c9-434c-8fb2-185a1b806e8f
-- title:
--   (24), p. 47 — 𝔹_ρ consists of the averages N⁻¹Σπᵢ with N⁻¹ΣE_πᵢ[𝔻(·, (x̂ᵢ, ŷᵢ))] ≤ ρ
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $(\hat x_i,\hat y_i)_{i\in[N]}$ the samples with $N\ge1$, and let the ground costs satisfy Assumption 2.4 for some $x_0$ and $\gamma>0$. Let $\rho\ge0$ and let $\mathbb Q$ be a probability measure on $\mathcal X\times\mathcal Y$. Then $\mathbb Q\in\mathbb B_\rho$ if and only if there are probability measures $\pi_1,\dots,\pi_N$ on $\mathcal X\times\mathcal Y$ with
--   $$\mathbb Q=\frac1N\sum_{i\in[N]}\pi_i\qquad\text{and}\qquad\frac1N\sum_{i\in[N]}\mathbb E_{\pi_i}\big[\mathbb D_{\mathcal X}(X,\hat x_i)+\mathbb D_{\mathcal Y}(Y,\hat y_i)\big]\le\rho.$$
--
--   This is the representation (24) of the transport ball from which the proofs of Propositions 4.2, 4.3 and Theorem 4.4 start: a coupling of $\mathbb Q$ with the empirical distribution splits into one conditional law $\pi_i$ per sample.
--
--   **Formalization Note.** The "only if" direction requires an optimal coupling, because $\mathbb W$ is an infimum and the constraint is the non-strict $\le\rho$; on Polish spaces with a continuous nonnegative cost such a coupling exists. The expectation of the cost is a lower Lebesgue integral of the $[0,\infty]$-valued cost.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 47, display (24); used on p. 48, proof of Theorem 4.4

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.FiberDual

theorem ball_repr {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Q : Measure (X × Y)) [IsProbabilityMeasure Q] :
    CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ↔
      ∃ π : Fin N → Measure (X × Y), (∀ i, IsProbabilityMeasure (π i)) ∧
        Q = (N : ENNReal)⁻¹ • ∑ i, π i ∧
        (N : ENNReal)⁻¹ * ∑ i, ∫⁻ z, CondPortOT.SingUninf.groundCost DX DY z (xh i, yh i) ∂(π i) ≤ ENNReal.ofReal ρ := by sorry

end CondPortOT.FiberDual
