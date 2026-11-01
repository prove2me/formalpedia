-- Prove2me | Theorems.Thm_CongestionTaxes_equilibrium_bound
-- name    : CongestionTaxes.equilibrium_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:51.252996+00:00
-- url     : https://prove2.me/theorems/d798054c-e62b-4526-aa76-cb71bc469b6c
-- title:
--   Proof of Theorem 3, pp.19–20 — every equilibrium costs at most $\rho\,\mathrm{MinCost}$
-- statement:
--   Let every cost in $\mathcal L$ satisfy Assumption 1 with $\rho=\sup_{\ell\in\mathcal L}\rho_\ell<\infty$, let $G$ be a congestion game with costs in $\mathcal L$, and let $\bigl((\bar y_i)_i,(\bar v_r)_r\bigr)$ be a solution of (12). Under the taxes of Definition 4 with parameters $\bar v$, every pure Nash, mixed Nash, correlated and coarse correlated equilibrium has (expected) social cost
--
--   $$
--   \mathbb E[\mathrm{SC}]\ \le\ \rho\,\mathrm{MinCost}(G).
--   $$
--
--   This is the passage from (13) to the price-of-anarchy bound of Theorem 3.
--
--   Differences from the source:
--
--   - encoding: the price-of-anarchy bound for pure Nash and, more generally, coarse correlated equilibria → $c\le\rho\,\mathrm{MinCost}(G)$ for every equilibrium social cost $c$ of each of the four classes; reason: multiplicative form with no division; the mixed and correlated classes lie between pure and coarse correlated (footnote 3)
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, proof of Theorem 3, pp.19–20

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_rhoSup
import Definitions.Def_CongestionTaxes_minCost
import Definitions.Def_CongestionTaxes_IsSolution
import Definitions.Def_CongestionTaxes_InClass
import Definitions.Def_CongestionTaxes_EqClass
import Definitions.Def_CongestionTaxes_equilibriumCosts

open scoped ENNReal

namespace CongestionTaxes

/-- Proof of Theorem 3, from (13) to the bound (Paccagnan, Gairing, arXiv:2105.07480v2, pp.19–20:
"Once (13) is shown, the desired bound on the price of anarchy follows readily for pure Nash
equilibria and more generally extends all the way to coarse correlated equilibria"). Let every
cost in `𝓛` satisfy Assumption 1 with `ρ = sup_{ℓ∈𝓛} ρ_ℓ < ∞`, let `G` be a game with costs in
`𝓛`, and let `(ȳ, v̄)` solve (12). Under the taxes of Definition 4 with parameters `v̄`, every
equilibrium of every class (pure Nash, mixed Nash, correlated, coarse correlated) has (expected)
social cost at most `ρ · MinCost(G)`.

**Formalization Note** Multiplicative form, with no ratio; `ρ` is `(rhoSup L).toReal`. -/
theorem equilibrium_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (L : Set (ℕ → ℝ)) (hL : ∀ ℓ ∈ L, Assumption1 ℓ) (hρ : rhoSup L < ⊤)
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hG : InClass L G)
    (y : ι → Finset E → ℝ) (v : E → ℝ) (hy : IsSolution G y v) (K : EqClass) :
    ∀ c ∈ equilibriumCosts K G v, c ≤ (rhoSup L).toReal * minCost G := by sorry

end CongestionTaxes
