-- Prove2me | Theorems.Thm_BlockchainMarketPower_f_strictConcaveOn
-- name    : BlockchainMarketPower.f_strictConcaveOn
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:52.636307+00:00
-- url     : https://prove2.me/theorems/8c9a3512-752b-4a70-ac23-f031a898a71c
-- title:
--   $\partial^2 f/\partial\Psi^2<0$: $f$ is strictly concave in $\Psi$
-- statement:
--   Let $\gamma'\in(0,1)$ and $0<P\le1$. For every $\Psi$,
--
--   $$
--   \frac{\partial^2 f(P,\Psi;\gamma')}{\partial\Psi^2}=-1+\frac{\gamma'}{4}\bigl(6\Psi^2-(6P+3)\Psi+(P+2)P\bigr),
--   $$
--
--   which on $[0,P]$ is at most $-1+\frac{3\gamma'}{4}<0$. Hence $\Psi\mapsto f(P,\Psi;\gamma')$ is strictly concave on $[0,P]$.
--
--   Strict concavity gives the uniqueness of the equilibrium supplier price.
--
--   Differences from the source:
--   - generalization: P = P∗ = 2α - 1 < 1, parameter γ → every P ∈ (0, 1] and every γ' ∈ (0, 1); reason: it contains P⋆_NB and P⋆_B, including P⋆_B = 1 at δ = 1, where the proof on p.39 refers back to this computation; the bound uses only P ≤ 1
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 3.1, p.35

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- `f` is strictly concave in `Ψ`, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of
Proposition 3.1, p.35: `∂²f/∂Ψ² = -1 + (γ'/4)(6Ψ² - (6P + 3)Ψ + (P + 2)P) ≤ -1 + 3γ'/4 < 0` on `[0, P]`.

**Formalization Note.** `P = 1` is included because `P⋆_B = 1` at `δ = 1`; the page's "(a)" says `P∗ < 1`,
but the bound uses only `P ≤ 1`. -/
theorem f_strictConcaveOn (P γ' : ℝ) (hγ₀ : 0 < γ') (hγ₁ : γ' < 1) (hP₀ : 0 < P) (hP₁ : P ≤ 1) :
    (∀ Ψ : ℝ, deriv (deriv (fun ψ => f P ψ γ')) Ψ =
        -1 + γ' / 4 * (6 * Ψ ^ 2 - (6 * P + 3) * Ψ + (P + 2) * P)) ∧
      (∀ Ψ ∈ Set.Icc 0 P,
        -1 + γ' / 4 * (6 * Ψ ^ 2 - (6 * P + 3) * Ψ + (P + 2) * P) ≤ -1 + 3 * γ' / 4) ∧
      -1 + 3 * γ' / 4 < 0 ∧
      StrictConcaveOn ℝ (Set.Icc 0 P) (fun Ψ => f P Ψ γ') := by sorry

end BlockchainMarketPower
