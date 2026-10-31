-- Prove2me | Theorems.Thm_BlockchainMarketPower_f_strictMonoOn_price
-- name    : BlockchainMarketPower.f_strictMonoOn_price
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:12.181101+00:00
-- url     : https://prove2.me/theorems/5899a831-0aee-441a-bf71-ff3e58469989
-- title:
--   $\partial f/\partial P>0$: $f$ is strictly increasing in $P$
-- statement:
--   Let $\gamma'\in(0,1)$ and $0<\Psi\le1$. For every $P$,
--
--   $$
--   \frac{\partial f(P,\Psi;\gamma')}{\partial P}=\frac\Psi2\Bigl(1-\frac{\gamma'}{2}(1-\Psi)(P-\Psi)\Bigr).
--   $$
--
--   For $P\in[\Psi,1]$ this derivative is at least $\frac\Psi2(1-\frac{\gamma'}2)>0$, and $P\mapsto f(P,\Psi;\gamma')$ is strictly increasing on $[\Psi,1]$.
--
--   This is why the manufacturer charges the largest price at which demand is positive.
--
--   Differences from the source:
--   - generalization: the domain 0 < Ψ < P ≤ 2α - 1, and γ, γ/N → Ψ ∈ (0, 1], P ∈ [Ψ, 1], every γ' ∈ (0, 1); reason: it contains both regimes (including P = 1 at δ = 1) and the printed domain
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 3.1, p.35, p.39

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- `f` is strictly increasing in `P`, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of
Proposition 3.1, p.35, p.39: `∂f/∂P = (Ψ/2)(1 - (γ'/2)(1 - Ψ)(P - Ψ)) ≥ (Ψ/2)(1 - γ'/2) > 0` for
`Ψ ≤ P ≤ 1`. -/
theorem f_strictMonoOn_price (Ψ γ' : ℝ) (hγ₀ : 0 < γ') (hγ₁ : γ' < 1) (hΨ₀ : 0 < Ψ) (hΨ₁ : Ψ ≤ 1) :
    (∀ P : ℝ, HasDerivAt (fun P => f P Ψ γ') (Ψ / 2 * (1 - γ' / 2 * (1 - Ψ) * (P - Ψ))) P) ∧
      (∀ P ∈ Set.Icc Ψ 1, Ψ / 2 * (1 - γ' / 2) ≤ Ψ / 2 * (1 - γ' / 2 * (1 - Ψ) * (P - Ψ))) ∧
      0 < Ψ / 2 * (1 - γ' / 2) ∧
      StrictMonoOn (fun P => f P Ψ γ') (Set.Icc Ψ 1) := by sorry

end BlockchainMarketPower
