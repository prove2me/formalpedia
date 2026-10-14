-- Prove2me | Theorems.Thm_CondPortOT_NullFiber_inf_mass_pos
-- name    : CondPortOT.NullFiber.inf_mass_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:09.708625+00:00
-- url     : https://prove2.me/theorems/db362dfc-c46b-4211-ae11-8f7f5d26aee3
-- title:
--   Proof of Proposition 4.3, p. 47 — for ρ < ρ_max the minimal fiber mass inf_{ℚ∈𝔹_ρ} ℚ(X ∈ 𝒩_γ(x₀)) is positive
-- statement:
--   Let $\gamma>0$, let Assumption 2.4 and the boundary regularity hold, and let $0\le\rho<\rho_{\max}(x_0,\gamma)$. Then the smallest mass that a distribution of the ambiguity set can put on the fiber is strictly positive:
--
--   $$\inf_{\mathbb Q\in\mathbb B_\rho}\mathbb Q\big(X\in\mathcal N_\gamma(x_0)\big)>0.$$
--
--   In words: with a budget below $\rho_{\max}$ the adversary cannot empty the fiber, not even approximately. This is the first step of the proof of Proposition 4.3.
--
--   **Formalization Note** The infimum is taken in $[0,\infty]$ over all probability measures in $\mathbb B_\rho$. The hypothesis $\rho\ge0$ is the paper's standing $\rho\in\mathbb R_+$.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 47, proof of Proposition 4.3, first sentence

import Mathlib
import Definitions.Def_CondPortOT_NullFiber_Setting

namespace CondPortOT.NullFiber

open MeasureTheory

theorem inf_mass_pos {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ)
    (hA : Assumption24 DX DY x0 γ xh) (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ < CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ) :
    0 < ⨅ (Q : Measure (X × Y)) (_ : CondPortOT.SingUninf.InBall DX DY xh yh ρ Q), Q (CondPortOT.SingUninf.fiber DX x0 γ) := by sorry

end CondPortOT.NullFiber
