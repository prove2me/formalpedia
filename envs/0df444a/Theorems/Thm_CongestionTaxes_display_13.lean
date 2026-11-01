-- Prove2me | Theorems.Thm_CongestionTaxes_display_13
-- name    : CongestionTaxes.display_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:36.940376+00:00
-- url     : https://prove2.me/theorems/e1add429-9c6e-4a6b-9d60-373e4b62a727
-- title:
--   Display (13), p.19 — fractional smoothness inequality
-- statement:
--   Let every cost in $\mathcal L$ satisfy Assumption 1 with $\rho=\sup_{\ell\in\mathcal L}\rho_\ell<\infty$, let $G$ be a congestion game with costs in $\mathcal L$ (nonempty strategy sets), let $\bigl((\bar y_i)_i,(\bar v_r)_r\bigr)$ be a solution of (12), and let $\bar C_i(a)=\sum_{r\in a_i}f_r(|a|_r,\bar v_r)$. Then for every profile $a\in\mathcal A$,
--
--   $$
--   \sum_{i=1}^N\sum_{k=1}^{s_i}\bar y_{i,k}\bigl[\bar C_i(a)-\bar C_i(a'_{i,k},a_{-i})\bigr]\ \ge\ \mathrm{SC}(a)-\rho\,\mathrm{SC}(a^{\mathrm{opt}}),
--   $$
--
--   where $\mathrm{SC}(a^{\mathrm{opt}})=\mathrm{MinCost}(G)$. Instead of comparing a profile with one deviation profile, as ordinary smoothness does, it is compared with the mixed profile $\bar y$ solving the relaxation.
--
--   Differences from the source:
--
--   - encoding: $\mathrm{SC}(a^{\mathrm{opt}})$ with $a^{\mathrm{opt}}\in\arg\min\mathrm{SC}$; $\rho$ → $\mathrm{MinCost}(G)$; the real number $\sup_\ell\rho_\ell$; reason: same values
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (13), proof of Theorem 3, p.19

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_rhoSup
import Definitions.Def_CongestionTaxes_taxedGame
import Definitions.Def_CongestionTaxes_minCost
import Definitions.Def_CongestionTaxes_IsSolution
import Definitions.Def_CongestionTaxes_InClass

open scoped ENNReal

namespace CongestionTaxes

/-- Display (13) (Paccagnan, Gairing, arXiv:2105.07480v2, proof of Theorem 3, p.19), the
fractional smoothness inequality. Let every cost in `𝓛` satisfy Assumption 1 with
`ρ = sup_{ℓ∈𝓛} ρ_ℓ < ∞`, let `G` be a congestion game with costs in `𝓛`, and let `(ȳ, v̄)` be a
solution of (12). With `C̄_i` the perceived cost under the taxes of Definition 4 with parameters
`v̄`, for every profile `a ∈ 𝓐`,
`∑_{i=1}^N ∑_{k=1}^{s_i} ȳ_{i,k} [C̄_i(a) − C̄_i(a'_{i,k}, a_{−i})] ≥ SC(a) − ρ SC(a^opt)`,
where `SC(a^opt) = MinCost(G)`.

**Formalization Note** `ρ` is `(rhoSup L).toReal`, and `SC(a^opt)` is `minCost G`. The actions
`a'_{i,k}` are the elements of `G.strategies i`. -/
theorem display_13 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (L : Set (ℕ → ℝ)) (hL : ∀ ℓ ∈ L, Assumption1 ℓ) (hρ : rhoSup L < ⊤)
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hG : InClass L G)
    (y : ι → Finset E → ℝ) (v : E → ℝ) (hy : IsSolution G y v)
    (a : ι → Finset E) (ha : CongestionPoA.AsymSum.IsProfile G a) :
    CongestionPoA.AsymSum.sumCost G a - (rhoSup L).toReal * minCost G ≤
      ∑ i, ∑ s ∈ G.strategies i, y i s *
        (CongestionPoA.AsymSum.cost (taxedGame G v) a i -
          CongestionPoA.AsymSum.cost (taxedGame G v) (Function.update a i s) i) := by sorry

end CongestionTaxes
