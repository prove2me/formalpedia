-- Prove2me | Theorems.Thm_CondPortOT_BigRadius_exists_measure_condExp_eq
-- name    : CondPortOT.BigRadius.exists_measure_condExp_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:18:04.58218+00:00
-- url     : https://prove2.me/theorems/983e4a6d-78c8-4bdf-a45c-83d14c16dd29
-- title:
--   Proof of Proposition 4.2, p. 46 (corrected) — for each y₀ some ℚ′ ∈ 𝔹_ρ with ℚ′(fiber) > 0 has E_ℚ′[ℓ | X ∈ 𝒩_γ(x₀)] = ℓ(y₀)
-- statement:
--   Let $\gamma>0$, let Assumption 2.4 hold and let $\rho>\rho_{\max}(x_0,\gamma)$. For every loss $\ell:\mathcal Y\to\mathbb R$ and every $y_0\in\mathcal Y$ there is a distribution $\mathbb Q'\in\mathbb B_\rho$ with $\mathbb Q'(X\in\mathcal N_\gamma(x_0))>0$ and
--   $$\mathbb E_{\mathbb Q'}\big[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)\big]=\ell(y_0).$$
--
--   Within the budget, an adversary can empty the fiber and then place an arbitrarily small mass at the single point $(x_0, y_0)$ inside it; the conditional law on the fiber is then the Dirac mass at $y_0$. This gives the lower bound in Proposition 4.2.
--
--   **Formalization Note** The construction printed on p. 46 keeps the mass $(1-\upsilon)\delta_{(\hat x_j,\hat y_j)}$ with $\hat x_j$ inside the fiber, so for it the fiber mass is $1/N$ and the conditional expectation is not $\ell(y_0)$. The statement here is the corrected conclusion the proof needs. It needs neither `BoundaryRegular` nor the closed form of $\rho_{\max}$: the hypothesis is about $\rho_{\max}$ as defined (an infimum over measures).
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 46–47, proof of Proposition 4.2 (construction of ℚ′, corrected)

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.BigRadius

theorem exists_measure_condExp_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ : rhoMax DX DY xh yh x0 γ < ENNReal.ofReal ρ) (L : Y → ℝ) (y0 : Y) :
    ∃ Q : Measure (X × Y), CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧ 0 < Q (CondPortOT.SingUninf.fiber DX x0 γ) ∧
      CondPortOT.SingUninf.condExp Q (CondPortOT.SingUninf.fiber DX x0 γ) L = (L y0 : EReal) := by sorry

end CondPortOT.BigRadius
