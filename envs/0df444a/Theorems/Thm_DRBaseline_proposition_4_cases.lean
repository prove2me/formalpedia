-- Prove2me | Theorems.Thm_DRBaseline_proposition_4_cases
-- name    : DRBaseline.proposition_4_cases
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:44.1062+00:00
-- url     : https://prove2.me/theorems/806bbba6-ea42-4c21-a501-d6bad01adace
-- title:
--   Cases 1–4 of the proof of Proposition 4, closed forms (corrected: sign and $c_s^2$ in Case 3): $X(b^*,r^*)$ against $X(\Lambda,r_0)$; the crossings are in proposition_4
-- statement:
--   Let $0<\Lambda<\Omega$, $c_s>0$, $\rho\in(0,1]$, $\Delta c>0$, $s$ any best-response selection, $(b^*,r^*)$ the least-rebate maximizer and $r_0$ an optimal normal-use rebate. Write $X^*=X(b^*,r^*)$, $X^*_0=X(\Lambda,r_0)$ and $r_{A0}=\frac23\bigl(4\Lambda c_s-\sqrt{\Lambda c_s(19\Lambda c_s-6\Delta c)}\bigr)$. Then
--
--   1. if $\Delta c\le\Lambda c_s/2$: $X^*_0=0<X^*$;
--   2. if $\Lambda c_s/2<\Delta c\le\min(3\Lambda c_s,5\Omega c_s/2)$: $X^*=\dfrac{3\rho(\Delta c)^2}{25\Omega c_s^2}$ and $X^*_0=\dfrac{\rho\Lambda r_{A0}}{2\Omega c_s}$;
--   3. if $3\Lambda c_s\le\Delta c<5\Omega c_s/2$: $X^*-X^*_0=\dfrac{2\rho(\Delta c)^2}{225\Omega c_s^2}$;
--   4. if $5\Omega c_s/2\le\Delta c$ and $\Lambda c_s/2<\Delta c\le3\Lambda c_s$: $X^*=\dfrac{\rho(\Delta c-\Omega c_s)(7\Omega c_s-\Delta c)}{9\Omega c_s^2}$ and $X^*_0=\dfrac{\rho\Lambda r_{A0}}{2\Omega c_s}$;
--   5. if $\max(3\Lambda c_s,5\Omega c_s/2)\le\Delta c\le3\Omega c_s$: $X^*-X^*_0=-\dfrac{\rho\bigl(2(\Delta c)^2-8\Omega\Delta c\,c_s+7\Omega^2c_s^2\bigr)}{9\Omega c_s^2}$;
--   6. if $3\Omega c_s<\Delta c<4\Omega c_s$: $X^*_0-X^*=\dfrac{\rho(4\Omega c_s-\Delta c)^2}{9\Omega c_s^2}$; and if $4\Omega c_s\le\Delta c$: $X^*_0=X^*=\rho\Omega$.
--
--   These are the computations from which the thresholds $c_D$ and $c_I$ of Proposition 4 are read off.
--
--   Differences from the source:
--
--   - correction: for cA1 ≤ ∆c < cB0, X∗ − X∗0 = ρ(2(∆c)² − 8Ω∆c cs + 7Ω²cs²)/(9Ωcs) → X∗ − X∗₀ = −ρ(2Δc² − 8ΩΔc c_s + 7Ω²c_s²)/(9Ωc_s²); reason: at Ω = c_s = 1, Λ = 1/2, Δc = 3: X∗ = 8ρ/9, X∗₀ = ρ, so X∗ − X∗₀ = −ρ/9 while the printed display gives +ρ/9; only the corrected sign agrees with the page's own 'X∗ ≥ X∗0 iff ∆c ≤ cx2'
--   - generalization: Case 1: ∆c < c0, r0 = X∗0 = 0 ≤ X∗; Case 3 displays on ∆c < cA1 and ∆c < cB0 → Δc ≤ c₀ with X∗₀ = 0 < X∗; item 5 on the closed range up to c_{B0}; reason: r₀ = 0 also at Δc = c₀ (p.OA2) and X∗ = 3ρΔc²/(25Ωc_s²) > 0; the display is continuous at c_{B0}; specializes to the printed ranges
--   - reading: Case 2 and the third sub-case of Case 3: X∗ and X∗0 convex increasing, with a unique crossing cx1 ∈ [c0, cB] (resp. cx3 ∈ [cA1, cA0]) → the closed forms of X∗ and X∗₀ on those ranges (items 2 and 4); the crossings themselves are clauses of the goal proposition_4; reason: the page gives no closed form for the crossings; the single-crossing conclusions are the content of Proposition 4 and are stated there once
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, Cases 1–4, p.OA3

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsLeastRebateOptimal
import Definitions.Def_DRBaseline_IsNormalUseOptimal
import Definitions.Def_DRBaseline_demandReduction

namespace DRBaseline

/-- **Cases 1–4 of the proof of Proposition 4 (corrected): `X(b∗, r∗)` against `X(Λ, r₀)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, Cases 1–4,
p.OA3.

Let `0 < Λ < Ω`, `c_s > 0`, `ρ ∈ (0, 1]`, `Δc > 0`, `s` any best-response selection,
`(b∗, r∗)` the least-rebate maximizer, `r₀` an optimal normal-use rebate,
`X∗ = X(b∗, r∗)`, `X∗₀ = X(Λ, r₀)` and `r_{A0} = (2/3)(4Λc_s − √(Λc_s(19Λc_s − 6Δc)))`.
1. (Case 1) If `Δc ≤ c₀ = Λc_s/2`: `X∗₀ = 0 < X∗`.
2. If `c₀ < Δc ≤ min(3Λc_s, 5Ωc_s/2)`: `X∗ = 3ρΔc²/(25Ωc_s²)` and `X∗₀ = ρΛr_{A0}/(2Ωc_s)`.
3. If `3Λc_s ≤ Δc < 5Ωc_s/2`: `X∗ − X∗₀ = 2ρΔc²/(225Ωc_s²)`.
4. If `5Ωc_s/2 ≤ Δc`, `c₀ < Δc ≤ 3Λc_s`: `X∗ = ρ(Δc − Ωc_s)(7Ωc_s − Δc)/(9Ωc_s²)` and
   `X∗₀ = ρΛr_{A0}/(2Ωc_s)`.
5. If `max(3Λc_s, 5Ωc_s/2) ≤ Δc ≤ 3Ωc_s`:
   `X∗ − X∗₀ = −ρ(2Δc² − 8ΩΔc c_s + 7Ω²c_s²)/(9Ωc_s²)`.
6. (Case 4) If `3Ωc_s < Δc < 4Ωc_s`: `X∗₀ − X∗ = ρ(4Ωc_s − Δc)²/(9Ωc_s²)`; if
   `4Ωc_s ≤ Δc`: `X∗₀ = X∗ = ρΩ`.

**Formalization Note** Item 5 corrects the printed display of Case 3, which has the opposite
sign and `9Ωc_s` in the denominator. Items 2 and 4 are the closed forms behind Case 2 and the
third sub-case of Case 3, whose crossing points the page only names. -/
theorem proposition_4_cases (Ω Λ cs ρ Δc : ℝ) (hΛ : 0 < Λ) (hΛΩ : Λ < Ω) (hcs : 0 < cs)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hΔc : 0 < Δc) (s : ℝ → ℝ → ℝ → ℝ)
    (hs : IsBestResponse Ω cs s) (b r r₀ : ℝ) (hbr : IsLeastRebateOptimal Ω ρ Δc s b r)
    (hr₀ : IsNormalUseOptimal Ω Λ ρ Δc s r₀) :
    (Δc ≤ Λ * cs / 2 →
      demandReduction Ω ρ s Λ r₀ = 0 ∧ 0 < demandReduction Ω ρ s b r) ∧
    (Λ * cs / 2 < Δc → Δc ≤ 3 * Λ * cs → Δc ≤ 5 * Ω * cs / 2 →
      demandReduction Ω ρ s b r = 3 * ρ * Δc ^ 2 / (25 * Ω * cs ^ 2) ∧
      demandReduction Ω ρ s Λ r₀ =
        ρ * Λ * (2 / 3 * (4 * Λ * cs - Real.sqrt (Λ * cs * (19 * Λ * cs - 6 * Δc)))) /
          (2 * Ω * cs)) ∧
    (3 * Λ * cs ≤ Δc → Δc < 5 * Ω * cs / 2 →
      demandReduction Ω ρ s b r - demandReduction Ω ρ s Λ r₀ =
        2 * ρ * Δc ^ 2 / (225 * Ω * cs ^ 2)) ∧
    (5 * Ω * cs / 2 ≤ Δc → Λ * cs / 2 < Δc → Δc ≤ 3 * Λ * cs →
      demandReduction Ω ρ s b r = ρ * (Δc - Ω * cs) * (7 * Ω * cs - Δc) / (9 * Ω * cs ^ 2) ∧
      demandReduction Ω ρ s Λ r₀ =
        ρ * Λ * (2 / 3 * (4 * Λ * cs - Real.sqrt (Λ * cs * (19 * Λ * cs - 6 * Δc)))) /
          (2 * Ω * cs)) ∧
    (3 * Λ * cs ≤ Δc → 5 * Ω * cs / 2 ≤ Δc → Δc ≤ 3 * Ω * cs →
      demandReduction Ω ρ s b r - demandReduction Ω ρ s Λ r₀ =
        -(ρ * (2 * Δc ^ 2 - 8 * Ω * Δc * cs + 7 * Ω ^ 2 * cs ^ 2) / (9 * Ω * cs ^ 2))) ∧
    (3 * Ω * cs < Δc → Δc < 4 * Ω * cs →
      demandReduction Ω ρ s Λ r₀ - demandReduction Ω ρ s b r =
        ρ * (4 * Ω * cs - Δc) ^ 2 / (9 * Ω * cs ^ 2)) ∧
    (4 * Ω * cs ≤ Δc →
      demandReduction Ω ρ s Λ r₀ = ρ * Ω ∧ demandReduction Ω ρ s b r = ρ * Ω) := by sorry

end DRBaseline
