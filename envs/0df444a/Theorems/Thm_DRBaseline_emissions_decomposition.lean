-- Prove2me | Theorems.Thm_DRBaseline_emissions_decomposition
-- name    : DRBaseline.emissions_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:20.164342+00:00
-- url     : https://prove2.me/theorems/bff425ee-97af-428f-9c88-b3eb71168da1
-- title:
--   Emissions decomposition $E_u=\bar E-\Delta e\,X(b,r)$
-- statement:
--   Let $0<\Lambda<\Omega$, $\Phi>0$, $c_s>0$, $\rho\in(0,1]$, emission intensities $e^h_g,e^l_g$ with $\Delta e=e^h_g-e^l_g$, and $s$ any best-response selection. For every $b\ge0$, $r\ge0$:
--
--   $$E_u(b,r)=\bar E(\rho,\Omega,\Lambda,\Phi,e^h_g,e^l_g)-E(b,r),\qquad E(b,r)=\Delta e\,X(b,r).$$
--
--   Each unit of actual demand reduction moves one unit from emission intensity $e^h_g$ to $e^l_g$, so total emissions fall linearly in the expected actual reduction.
--
--   Differences from the source:
--
--   - encoding: E(b,r) = ρE[(e^h_g − e^l_g)s∗] → Δe · X(b, r); reason: X already contains the factor ρ
--   - encoding: expectations over ω, λ, φ → iterated interval integrals with the uniform densities written out, for an arbitrary best-response selection; reason: Lean convention; ties are null sets
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.5, p.11; Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, pp.OA3–OA4

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_demandReduction
import Definitions.Def_DRBaseline_noProgramEmissions
import Definitions.Def_DRBaseline_totalEmissions

namespace DRBaseline

/-- **Emissions decomposition `E_u = Ē − E(b, r)` with `E(b, r) = Δe · X(b, r)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.5, p.11; Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4,
pp.OA3–OA4.

For emission intensities `e^h_g`, `e^l_g` with `Δe = e^h_g − e^l_g`, every best-response
selection `s`, every `b ≥ 0` and `r ≥ 0`:
$$E_u(b,r) = \bar E(\rho,\Omega,\Lambda,\Phi,e^h_g,e^l_g) - \Delta e\, X(b,r).$$

**Formalization Note** `E(b, r) = ρE[Δe s∗] = Δe·X(b, r)`: the factor `ρ` is already inside
`X`. No sign condition on `Δe` is needed. -/
theorem emissions_decomposition (ρ Ω Λ Φ cs ehg elg : ℝ) (hΩ : 0 < Ω) (hΛ : 0 < Λ)
    (hΛΩ : Λ < Ω) (hΦ : 0 < Φ) (hcs : 0 < cs) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) (b r : ℝ) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    totalEmissions ρ Ω Λ Φ ehg elg s b r =
      noProgramEmissions ρ Ω Λ Φ ehg elg - (ehg - elg) * demandReduction Ω ρ s b r := by sorry

end DRBaseline
