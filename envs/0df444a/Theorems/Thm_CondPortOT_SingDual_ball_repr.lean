-- Prove2me | Theorems.Thm_CondPortOT_SingDual_ball_repr
-- name    : CondPortOT.SingDual.ball_repr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:53.372787+00:00
-- url     : https://prove2.me/theorems/0c6ff197-b717-4151-bbfd-a9fc0e7fb630
-- title:
--   (24), p. 47 — 𝔹_ρ is the set of averages N⁻¹Σπᵢ of probability measures with N⁻¹ΣE_πᵢ[𝔻(·,(x̂ᵢ,ŷᵢ))] ≤ ρ
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $N\ge1$ samples $(\hat x_i,\hat y_i)$, ground costs satisfying Assumption 2.4, and $\rho\ge0$. For every probability measure $\mathbb Q$ on $\mathcal X\times\mathcal Y$, $\mathbb Q\in\mathbb B_\rho$ (that is, $\mathbb W(\mathbb Q,\hat{\mathbb P})\le\rho$) if and only if there are probability measures $\pi_1,\dots,\pi_N$ on $\mathcal X\times\mathcal Y$ with
--   $$\mathbb Q=\frac1N\sum_{i\in[N]}\pi_i,\qquad \frac1N\sum_{i\in[N]}\mathbb E_{\pi_i}\big[\mathbb D_{\mathcal X}(X,\hat x_i)+\mathbb D_{\mathcal Y}(Y,\hat y_i)\big]\le\rho .$$
--
--   This decomposition of the ambiguity set is the starting point of every proof of the paper: it turns a statement about couplings with the empirical measure into a statement about $N$ separate measures, one per sample.
--
--   **Formalization Note** The "only if" direction needs the transport infimum to be attained (an optimal coupling exists for a continuous non-negative cost on Polish spaces); the definition of $\mathbb W$ is an infimum, so attainment is part of what is to be proved, not assumed. The expectations are lower integrals of the $[0,\infty]$-valued cost. The fiber parameters $x_0,\gamma$ enter only through the standing Assumption 2.4.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 47, display (24) (proof of Proposition 4.3); same set displayed on p. 40; used on p. 36 (proof of Proposition A.5)

import Mathlib
import Definitions.Def_CondPortOT_SingDual_Setting

open MeasureTheory

namespace CondPortOT.SingDual

theorem ball_repr {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hA : Assumption24 DX DY x0 γ xh) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (Q : Measure (X × Y)) [IsProbabilityMeasure Q] :
    CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ↔
      ∃ π : Fin N → Measure (X × Y), (∀ i, IsProbabilityMeasure (π i)) ∧
        Q = (N : ENNReal)⁻¹ • ∑ i, π i ∧
        (N : ENNReal)⁻¹ * ∑ i, ∫⁻ z, CondPortOT.SingUninf.groundCost DX DY z (xh i, yh i) ∂(π i) ≤
          ENNReal.ofReal ρ := by sorry

end CondPortOT.SingDual
