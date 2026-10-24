-- Prove2me | Theorems.Thm_CondPortOT_FiberDual_proposition_2_5
-- name    : CondPortOT.FiberDual.proposition_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:58.595304+00:00
-- url     : https://prove2.me/theorems/5945d2d0-379f-4444-bb2f-57bd693f8029
-- title:
--   Proposition 2.5 — ρ_min is the value of a fractional knapsack LP, and 𝔹_ρ meets the fiber constraint iff ρ ≥ ρ_min
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $N\ge1$ samples $(\hat x_i,\hat y_i)$, $x_0\in\mathcal X$, $\gamma\ge0$, and let Assumption 2.4 hold. Let $\varepsilon\in[0,1]$ and let $\kappa_i=\inf_{x\in\mathcal N_\gamma(x_0)}\mathbb D_{\mathcal X}(x,\hat x_i)$ as in (7). Then
--
--   1. the minimum radius equals the optimal value of a linear program, and that minimum is attained:
--   $$\rho_{\min}(x_0,\gamma,\varepsilon)=\min\Big\{N^{-1}\sum_{i\in[N]}\kappa_i\upsilon_i:\ \upsilon\in[0,1]^N,\ \sum_{i\in[N]}\upsilon_i\ge N\varepsilon\Big\};$$
--   2. for every $\rho\ge0$, there exists $\mathbb Q\in\mathbb B_\rho$ with $\mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\varepsilon$ if and only if $\rho\ge\rho_{\min}(x_0,\gamma,\varepsilon)$.
--
--   The second part is what makes the supremum of Theorem 4.4 range over a nonempty set when $\rho>\rho_{\min}$, and the proof of Theorem 4.4 uses it to certify strong LP duality.
--
--   **Formalization Note.** $\rho_{\min}$ is an infimum in $[0,\infty]$ and is compared with $\rho$ through `ENNReal.ofReal`. The restriction $\varepsilon\le1$ is the paper's standing range $\varepsilon\in[0,1]$ (p. 9); it makes the linear program feasible.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 11, Proposition 2.5, display (9); used on p. 51, proof of Theorem 4.4

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.FiberDual

theorem proposition_2_5 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 ≤ γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∃ v : ℝ,
      IsLeast {r : ℝ | ∃ υ : Fin N → ℝ, (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧
        (N : ℝ) * ε ≤ ∑ i, υ i ∧ r = (N : ℝ)⁻¹ * ∑ i, CondPortOT.SingUninf.kappa DX x0 γ xh i * υ i} v ∧
      CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε = ENNReal.ofReal v) ∧
    ∀ ρ : ℝ, 0 ≤ ρ →
      ((∃ Q : Measure (X × Y), CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧ ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ)) ↔
        CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε ≤ ENNReal.ofReal ρ) := by sorry

end CondPortOT.FiberDual
