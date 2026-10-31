-- Prove2me | Theorems.Thm_DRBaseline_proposition_4
-- name    : DRBaseline.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:43.699662+00:00
-- url     : https://prove2.me/theorems/145df46c-b967-4180-95d3-072a8a40a90d
-- title:
--   Proposition 4 (corrected: emissions as total $E_u$, switch of $c_I$): inflation lowers demand reduction and raises emissions iff $\Delta c\ge c_I$; deflation does the reverse iff $\Delta c\le c_D$
-- statement:
--   Fix $0<\Lambda<\Omega$ and $c_s>0$. There are cost thresholds $c_I$ and $c_D$, depending only on $\Omega,\Lambda,c_s$, with
--
--   1. $\Lambda c_s/2<c_D<5\Lambda c_s/3<c_I<4\Omega c_s$;
--   2. $c_D=\kappa\Lambda c_s$, where $\kappa\in(1/2,1)$ is the root of $9\kappa^3+15\kappa^2-175\kappa+125=0$ ($\kappa\approx0.7941$);
--   3. $c_I=\tfrac12(4+\sqrt2)\,\Omega c_s$ if $\Lambda\le\frac{4+\sqrt2}{6}\Omega$; otherwise $\tfrac52\Omega c_s\le c_I\le3\Lambda c_s$ and
--   $$\frac{(c_I-\Omega c_s)(7\Omega c_s-c_I)}{9\Omega c_s^2}=\frac{\Lambda}{2\Omega c_s}\cdot\frac23\Bigl(4\Lambda c_s-\sqrt{\Lambda c_s(19\Lambda c_s-6c_I)}\Bigr),$$
--
--   such that the following holds for every event probability $\rho\in(0,1]$, mean off-peak demand $\Phi>0$, marginal costs $c^l_p<c^h_p$ with $\Delta c=c^h_p-c^l_p$, every best-response selection of the customers, the least-rebate maximizer $(b^*,r^*)$ of the net savings $C$ and every optimal rebate $r_0$ at the normal-use baseline $b=\Lambda$:
--
--   1. **Inflation** ($b^*>\Lambda$): $X(b^*,r^*)\le X(\Lambda,r_0)$ if and only if $\Delta c\ge c_I$.
--   2. **Deflation** ($b^*<\Lambda$): $X(b^*,r^*)\ge X(\Lambda,r_0)$ if and only if $\Delta c\le c_D$.
--   3. If $b^*\le\Lambda$: $X(b^*,r^*)>X(\Lambda,r_0)$ if and only if $\Delta c<c_D$.
--   4. For emission intensities $e^l_g<e^h_g$, total expected emissions satisfy: under inflation, $E_u(b^*,r^*)\ge E_u(\Lambda,r_0)$ iff $\Delta c\ge c_I$; under deflation, $E_u(b^*,r^*)\le E_u(\Lambda,r_0)$ iff $\Delta c\le c_D$.
--
--   So optimizing the baseline, which always raises the firm's savings, can lower the actual demand reduction and raise emissions: with inflation exactly when the cost gap is large, and deflation does the reverse exactly when it is small.
--
--   Differences from the source:
--
--   - correction: higher emissions (E(b∗,r∗) ≥ E(Λ,r0)) → E_u(b∗, r∗) ≥ E_u(Λ, r₀), total expected emissions; reason: §3.5 defines E as the reduction in emissions, so the printed inequality points the wrong way: at Ω = c_s = 1, Λ = 1/2, Δc = 7/2, ρ = 1/2, Δe > 0, (b∗, r∗) = (7/6, 5/3), r₀ = 4, X∗ = 35ρ/36 < ρ = X₀, so E(b∗,r∗) < E(Λ,r₀) although Δc ≥ c_I
--   - correction: cI = cx2 = ½(4 + √2)Ωcs if Λ < (2/3 + 1/(2√3))Ω, cI = cx3 otherwise (proof, p.OA3) → c_I = ½(4 + √2)Ωc_s if Λ ≤ ((4 + √2)/6)Ω, and the root c_x3 ∈ [c_{A1}, c_{A0}] otherwise; reason: the formula behind c_x2 needs Δc ≥ c_{A0}; at Ω = c_s = 1, Λ = 14/15, Δc = 54823/20160 > c_x2: r₀ = 31/18, X₀ = 217ρ/270 < X∗ ≈ 0.8178ρ, so inflation does not lower the reduction there
--   - generalization: thresholds cI(Ω,Λ,cs) and cD(Λ,cs) exist → c_I and c_D are pinned down: their order, c_D = κΛc_s with κ the cubic's root in (1/2, 1), and the formulas or equation for c_I; reason: implies the printed existence; c_D depends on Λ, c_s only, as printed
--   - reading: inflation / deflation of the baseline → b∗ > Λ / b∗ < Λ strictly, plus clause 3 on b∗ ≤ Λ with strict inequalities; reason: p.17 defines inflation as b∗ > Λ and deflation as b∗ < Λ; with b∗ ≤ Λ and weak inequalities the iff fails at Δc = c_B, where X∗ = X₀ but Δc > c_D; clause 3 is the form the proof ends with
--   - reading: (b∗, r∗) = arg max C → the least-rebate maximizer; reason: for Δc ≥ 4Ωc_s the maximizer is not unique; X is the same on the whole maximizer set
--   - reading: Δe = e^h_g − e^l_g, no sign stated → e^l_g < e^h_g in the emissions clause; reason: p.10: emissions-intensive plants run during events; with Δe ≤ 0 the emissions clause reverses or is empty
--   - reading: event probability ρ → 0 < ρ ≤ 1; reason: with ρ = 0 no event occurs and the iffs fail
--   - encoding: ∆c = c^h_p − c^l_p > 0; s∗ and r0 as arg max → chp − clp with clp < chp; an arbitrary best-response selection and every optimal r₀; reason: Lean convention; ties are null sets and r₀ is unique
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Proposition 4, p.19; proof pp.OA3–OA4

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsLeastRebateOptimal
import Definitions.Def_DRBaseline_IsNormalUseOptimal
import Definitions.Def_DRBaseline_demandReduction
import Definitions.Def_DRBaseline_totalEmissions

namespace DRBaseline

/-- **Proposition 4 (corrected: emissions as total emissions `E_u`): baseline inflation lowers the
demand reduction and raises emissions exactly when `Δc ≥ c_I`; deflation raises the reduction
and lowers emissions exactly when `Δc ≤ c_D`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Proposition 4, p.19; proof pp.OA3–OA4.

Fix `0 < Λ < Ω` and `c_s > 0`. There are thresholds `c_I`, `c_D`, depending on `Ω, Λ, c_s`
only, with
* `Λc_s/2 < c_D < 5Λc_s/3 < c_I < 4Ωc_s`;
* `c_D = κΛc_s` with `κ ∈ (1/2, 1)` the root of `9κ³ + 15κ² − 175κ + 125 = 0`;
* `c_I = ½(4 + √2)Ωc_s` if `Λ ≤ ((4 + √2)/6)Ω`, and otherwise `5Ωc_s/2 ≤ c_I ≤ 3Λc_s` with
  `(c_I − Ωc_s)(7Ωc_s − c_I)/(9Ωc_s²) = (Λ/(2Ωc_s))·(2/3)(4Λc_s − √(Λc_s(19Λc_s − 6c_I)))`,

such that for every `ρ ∈ (0, 1]`, `Φ > 0`, marginal costs `c^l_p < c^h_p` (`Δc = c^h_p − c^l_p`),
every best-response selection `s`, the least-rebate maximizer `(b∗, r∗)` of `C` and every
optimal normal-use rebate `r₀`:
1. if `b∗ > Λ` (inflation): `X(b∗, r∗) ≤ X(Λ, r₀)` iff `Δc ≥ c_I`;
2. if `b∗ < Λ` (deflation): `X(Λ, r₀) ≤ X(b∗, r∗)` iff `Δc ≤ c_D`;
3. if `b∗ ≤ Λ`: `X(Λ, r₀) < X(b∗, r∗)` iff `Δc < c_D`;
4. for emission intensities `e^l_g < e^h_g`: under inflation, `E_u(b∗, r∗) ≥ E_u(Λ, r₀)` iff
   `Δc ≥ c_I`; under deflation, `E_u(b∗, r∗) ≤ E_u(Λ, r₀)` iff `Δc ≤ c_D`.

**Formalization Note** The printed emissions clause compares `E(b, r) = ρE[Δe s∗]`, which §3.5
defines as the *reduction* in emissions; "higher emissions" is stated for total emissions `E_u`.
The thresholds are pinned down (the page only names them), and the page's `c_I` switches form
at `Λ = (2/3 + 1/(2√3))Ω`; the correct switch is at `((4 + √2)/6)Ω`. Inflation and deflation
are the strict `b∗ > Λ`, `b∗ < Λ` of p.17. -/
theorem proposition_4 (Ω Λ cs : ℝ) (hΛ : 0 < Λ) (hΛΩ : Λ < Ω) (hcs : 0 < cs) :
    ∃ cI cD : ℝ,
      Λ * cs / 2 < cD ∧ cD < 5 * Λ * cs / 3 ∧ 5 * Λ * cs / 3 < cI ∧ cI < 4 * Ω * cs ∧
      (∃ κ : ℝ, 1 / 2 < κ ∧ κ < 1 ∧ 9 * κ ^ 3 + 15 * κ ^ 2 - 175 * κ + 125 = 0 ∧
        cD = κ * Λ * cs) ∧
      (Λ ≤ (4 + Real.sqrt 2) / 6 * Ω → cI = (4 + Real.sqrt 2) / 2 * Ω * cs) ∧
      ((4 + Real.sqrt 2) / 6 * Ω < Λ →
        5 * Ω * cs / 2 ≤ cI ∧ cI ≤ 3 * Λ * cs ∧
        (cI - Ω * cs) * (7 * Ω * cs - cI) / (9 * Ω * cs ^ 2) =
          Λ / (2 * Ω * cs) *
            (2 / 3 * (4 * Λ * cs - Real.sqrt (Λ * cs * (19 * Λ * cs - 6 * cI))))) ∧
      ∀ ρ Φ chp clp : ℝ, 0 < ρ → ρ ≤ 1 → 0 < Φ → clp < chp →
      ∀ s : ℝ → ℝ → ℝ → ℝ, IsBestResponse Ω cs s →
      ∀ b r : ℝ, IsLeastRebateOptimal Ω ρ (chp - clp) s b r →
      ∀ r₀ : ℝ, IsNormalUseOptimal Ω Λ ρ (chp - clp) s r₀ →
        (Λ < b → (demandReduction Ω ρ s b r ≤ demandReduction Ω ρ s Λ r₀ ↔
          cI ≤ chp - clp)) ∧
        (b < Λ → (demandReduction Ω ρ s Λ r₀ ≤ demandReduction Ω ρ s b r ↔
          chp - clp ≤ cD)) ∧
        (b ≤ Λ → (demandReduction Ω ρ s Λ r₀ < demandReduction Ω ρ s b r ↔
          chp - clp < cD)) ∧
        ∀ ehg elg : ℝ, elg < ehg →
          (Λ < b → (totalEmissions ρ Ω Λ Φ ehg elg s Λ r₀ ≤
              totalEmissions ρ Ω Λ Φ ehg elg s b r ↔ cI ≤ chp - clp)) ∧
          (b < Λ → (totalEmissions ρ Ω Λ Φ ehg elg s b r ≤
              totalEmissions ρ Ω Λ Φ ehg elg s Λ r₀ ↔ chp - clp ≤ cD)) := by sorry

end DRBaseline
