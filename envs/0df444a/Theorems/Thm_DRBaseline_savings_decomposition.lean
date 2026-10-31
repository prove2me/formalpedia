-- Prove2me | Theorems.Thm_DRBaseline_savings_decomposition
-- name    : DRBaseline.savings_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:53.28552+00:00
-- url     : https://prove2.me/theorems/af81e497-fbe9-49cd-8579-2210fa65d786
-- title:
--   Decompositions $C_u=\bar C-C$ and $C=(\Delta c-r)X-rX_o+rX_u$
-- statement:
--   Let $0<\Lambda<\Omega$, $\Phi>0$, $c_s>0$, $\rho\in(0,1]$, marginal costs $c^l_p<c^h_p$ with $\Delta c=c^h_p-c^l_p$, and $s$ any best-response selection. For every $b\ge0$, $r\ge0$:
--
--   $$C_u(b,r)=\bar C(\rho,\Omega,\Lambda,\Phi,c^h_p,c^l_p)-C(b,r),$$
--
--   $$C(b,r)=(\Delta c-r)\,X(b,r)-r\,X_o(b)+r\,X_u(b,r).$$
--
--   The first identity shows that minimizing the total cost is maximizing the net savings. The second splits the savings into procurement savings on the actual reduction, an overestimation penalty and an underestimation benefit.
--
--   Differences from the source:
--
--   - encoding: expectations over ω, λ, φ → iterated interval integrals with the uniform densities written out, for an arbitrary best-response selection; reason: Lean convention; ties are null sets
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.4, p.10; §4, p.14; Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, pp.OA1–OA2

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_demandReduction
import Definitions.Def_DRBaseline_overestimation
import Definitions.Def_DRBaseline_underestimation
import Definitions.Def_DRBaseline_netSavings
import Definitions.Def_DRBaseline_noProgramCost
import Definitions.Def_DRBaseline_totalCost

namespace DRBaseline

/-- **Decompositions of the firm's cost: `C_u = C̄ − C` and `C = (Δc − r)X − rX_o + rX_u`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.4, p.10; §4, p.14; Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3,
and 4, pp.OA1–OA2.

For marginal costs `c^h_p`, `c^l_p` with `Δc = c^h_p − c^l_p`, every best-response selection
`s`, every `b ≥ 0` and `r ≥ 0`:
$$C_u(b,r) = \bar C(\rho,\Omega,\Lambda,\Phi,c^h_p,c^l_p) - C(b,r),\qquad
C(b,r) = (\Delta c - r)X(b,r) - rX_o(b) + rX_u(b,r).$$
Hence minimizing `C_u` over `(b, r)` is the same as maximizing `C`.

**Formalization Note** Both identities hold for every selection of best responses. -/
theorem savings_decomposition (ρ Ω Λ Φ cs chp clp : ℝ) (hΩ : 0 < Ω) (hΛ : 0 < Λ)
    (hΛΩ : Λ < Ω) (hΦ : 0 < Φ) (hcs : 0 < cs) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : clp < chp)
    (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) (b r : ℝ) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    totalCost ρ Ω Λ Φ chp clp s b r =
        noProgramCost ρ Ω Λ Φ chp clp - netSavings Ω ρ (chp - clp) s b r ∧
    netSavings Ω ρ (chp - clp) s b r =
        (chp - clp - r) * demandReduction Ω ρ s b r - r * overestimation Ω ρ b +
          r * underestimation Ω cs ρ b r := by sorry

end DRBaseline
