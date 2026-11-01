-- Prove2me | Theorems.Thm_CongestionTaxes_approx_solution_bound
-- name    : CongestionTaxes.approx_solution_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:46.332487+00:00
-- url     : https://prove2.me/theorems/d3c77755-c4e5-4604-8fa2-bcd1ced459b4
-- title:
--   Proof of Theorem 3, p.20 — $(1+\xi)$-approximate solutions give $(1+\xi)\rho$
-- statement:
--   Let every cost in $\mathcal L$ satisfy Assumption 1 with $\rho=\sup_{\ell\in\mathcal L}\rho_\ell<\infty$, let $G$ be a congestion game with costs in $\mathcal L$, let $\xi\ge0$, and let $\bigl((y_i)_i,(v_r)_r\bigr)$ be a $(1+\xi)$-approximate solution of (12). Under the taxes with parameters $v$:
--
--   1. for every profile $a\in\mathcal A$, $\sum_i\sum_k y_{i,k}\bigl[\bar C_i(a)-\bar C_i(a'_{i,k},a_{-i})\bigr]\ge\mathrm{SC}(a)-(1+\xi)\rho\,\mathrm{MinCost}(G)$;
--   2. every pure Nash, mixed Nash, correlated and coarse correlated equilibrium has (expected) social cost at most $(1+\xi)\rho\,\mathrm{MinCost}(G)$.
--
--   This is the second claim of Theorem 3 before $\xi$ is chosen.
--
--   Differences from the source:
--
--   - generalization: $\xi>0$ → $\xi\ge0$; reason: $\xi=0$ is the first claim
--   - reading: (12) solved to arbitrary precision → a feasible point whose objective is at most $1+\xi$ times that of every feasible point; reason: the fifth line of (14) pays exactly a multiplicative factor $1+\xi$ (p.20)
--   - encoding: the price of anarchy $(1+\xi)\rho$ → $c\le(1+\xi)\rho\,\mathrm{MinCost}(G)$ for every equilibrium social cost $c$ of each class; reason: multiplicative form with no division
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, proof of Theorem 3, second claim, p.20

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_rhoSup
import Definitions.Def_CongestionTaxes_taxedGame
import Definitions.Def_CongestionTaxes_minCost
import Definitions.Def_CongestionTaxes_IsApproxSolution
import Definitions.Def_CongestionTaxes_InClass
import Definitions.Def_CongestionTaxes_EqClass
import Definitions.Def_CongestionTaxes_equilibriumCosts

open scoped ENNReal

namespace CongestionTaxes

/-- Proof of Theorem 3, second claim (Paccagnan, Gairing, arXiv:2105.07480v2, p.20: "the argument
in Eq. (14) will go through with a minor change on the fifth line, where one pays a multiplicative
factor 1 + ξ ... Correspondingly, we obtain a price of anarchy of (1 + ξ)ρ in place of ρ"). Let
every cost in `𝓛` satisfy Assumption 1 with `ρ = sup_{ℓ∈𝓛} ρ_ℓ < ∞`, let `G` be a game with costs
in `𝓛`, let `ξ ≥ 0`, and let `(y, v)` be a `(1 + ξ)`-approximate solution of (12). Under the taxes of
Definition 4 with parameters `v`:
1. (13) holds with `(1 + ξ)ρ` in place of `ρ`, for every profile `a ∈ 𝓐`;
2. every equilibrium of every class has (expected) social cost at most `(1 + ξ)ρ · MinCost(G)`. -/
theorem approx_solution_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (L : Set (ℕ → ℝ)) (hL : ∀ ℓ ∈ L, Assumption1 ℓ) (hρ : rhoSup L < ⊤)
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hG : InClass L G)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (y : ι → Finset E → ℝ) (v : E → ℝ) (hy : IsApproxSolution ξ G y v) :
    (∀ a, CongestionPoA.AsymSum.IsProfile G a →
      CongestionPoA.AsymSum.sumCost G a - (1 + ξ) * (rhoSup L).toReal * minCost G ≤
        ∑ i, ∑ s ∈ G.strategies i, y i s *
          (CongestionPoA.AsymSum.cost (taxedGame G v) a i -
            CongestionPoA.AsymSum.cost (taxedGame G v) (Function.update a i s) i)) ∧
    ∀ K : EqClass, ∀ c ∈ equilibriumCosts K G v, c ≤ (1 + ξ) * (rhoSup L).toReal * minCost G := by sorry

end CongestionTaxes
