-- Prove2me | Theorems.Thm_DRBaseline_demandReduction_closed_form
-- name    : DRBaseline.demandReduction_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:26.467434+00:00
-- url     : https://prove2.me/theorems/0e6750f5-8d00-4ba4-883a-a4f675ac5df9
-- title:
--   Closed form of the expected demand reduction $X(b,r)$
-- statement:
--   Let $\Omega>0$, $c_s>0$, $\rho\in(0,1]$, $s$ any best-response selection, $b\ge0$ and $r\ge0$. Then
--
--   1. if $\omega_1(b,r)<2\Omega$: $\displaystyle X(b,r)=X_1(b,r)=\frac{\rho\,br}{2\Omega c_s}$;
--   2. if $\omega_1(b,r)=2\Omega$ and $r\le2\Omega c_s$: $\displaystyle X(b,r)=X_2(r)=\frac{\rho\,r(4\Omega c_s-r)}{4\Omega c_s^2}$;
--   3. if $\omega_1(b,r)=2\Omega$ and $r>2\Omega c_s$: $X(b,r)=\rho\Omega$ (every customer shifts all of its demand).
--
--   These closed forms are what the firm's optimization runs on.
--
--   Differences from the source:
--
--   - reading: X2 for ω2 < 2Ω (or, equivalently, for r ≤ 2Ωc_s), ρΩ otherwise → X₂ for r ≤ 2Ωc_s, ρΩ for r > 2Ωc_s (both when ω₁ = 2Ω); reason: the page gives both conditions as equivalent; they differ only at r = 2Ωc_s, where X₂ = ρΩ, so both readings give the same values
--   - encoding: ρ ∫_0^{2Ω} s∗ f(ω) dω → interval integral with f = 1/(2Ω) written out, for an arbitrary best-response selection; reason: Lean convention; ties are null sets
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_omega1
import Definitions.Def_DRBaseline_demandReduction

namespace DRBaseline

/-- **Closed form of the expected demand reduction `X(b, r)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1.

For every best-response selection `s`, `b ≥ 0`, `r ≥ 0`:
1. if `ω₁(b, r) < 2Ω`, then `X(b, r) = X₁(b, r) = ρbr/(2Ωc_s)`;
2. if `ω₁(b, r) = 2Ω` and `r ≤ 2Ωc_s`, then `X(b, r) = X₂(r) = ρr(4Ωc_s − r)/(4Ωc_s²)`;
3. if `ω₁(b, r) = 2Ω` and `r > 2Ωc_s`, then `X(b, r) = ρΩ`.

**Formalization Note** The page conditions the second and third cases on "ω2 < 2Ω (or,
equivalently for r ≤ 2Ωcs)"; the Lean uses the rebate form. At `r = 2Ωc_s` both formulas give
`ρΩ`. -/
theorem demandReduction_closed_form (Ω cs ρ : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) (b r : ℝ) (hb : 0 ≤ b)
    (hr : 0 ≤ r) :
    (omega1 Ω cs b r < 2 * Ω → demandReduction Ω ρ s b r = ρ * (b * r) / (2 * Ω * cs)) ∧
    (omega1 Ω cs b r = 2 * Ω → r ≤ 2 * Ω * cs →
      demandReduction Ω ρ s b r = ρ * (r * (4 * Ω * cs - r)) / (4 * Ω * cs ^ 2)) ∧
    (omega1 Ω cs b r = 2 * Ω → 2 * Ω * cs < r → demandReduction Ω ρ s b r = ρ * Ω) := by sorry

end DRBaseline
