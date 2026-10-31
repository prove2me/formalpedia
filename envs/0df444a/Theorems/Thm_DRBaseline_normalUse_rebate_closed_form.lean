-- Prove2me | Theorems.Thm_DRBaseline_normalUse_rebate_closed_form
-- name    : DRBaseline.normalUse_rebate_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:24.401107+00:00
-- url     : https://prove2.me/theorems/5d6468d6-cbeb-4f14-ab2e-87a5d79dab3c
-- title:
--   Closed form of the normal-use rebate $r_0$
-- statement:
--   Let $0<\Lambda<\Omega$, $c_s>0$, $\rho\in(0,1]$, $\Delta c>0$ and $s$ any best-response selection. With $c_0=\Lambda c_s/2$, $c_{A0}=3\Lambda c_s$, $c_{B0}=3\Omega c_s$ and
--
--   $$r_{A0}=\tfrac23\Bigl(4\Lambda c_s-\sqrt{\Lambda c_s(19\Lambda c_s-6\Delta c)}\Bigr),\qquad r_{B0}=\frac{2(\Delta c)^2}{9\Lambda c_s},\qquad r_{C0}=\frac{2\Omega^2c_s}{\Lambda},$$
--
--   the problem $\max_{r\ge0}C(\Lambda,r)$ has exactly one solution $r_0$, and
--
--   $$r_0=\begin{cases}0 & \Delta c\le c_0,\\ r_{A0} & c_0<\Delta c\le c_{A0},\\ r_{B0} & c_{A0}<\Delta c\le c_{B0},\\ r_{C0} & c_{B0}<\Delta c.\end{cases}$$
--
--   Differences from the source:
--
--   - generalization: r0 = 0 for ∆c ≤ c0 because C0 decreases in r; unique maximizers rA0, rB0; r0 = rC0 for ∆c > cB0 → for every r₀: r₀ is optimal if and only if it equals the piecewise value, so the maximizer exists and is unique on every branch; reason: the iff specializes to the page's r₀ on each branch and adds uniqueness on the first and last
--   - encoding: max_r C(Λ, r) → maximum over r ≥ 0; reason: the firm's domain
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, p.OA2

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsNormalUseOptimal

namespace DRBaseline

/-- **Closed form of the normal-use rebate `r₀`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, p.OA2.

Let `0 < Λ < Ω`, `c_s > 0`, `ρ ∈ (0, 1]`, `Δc > 0`, and let `s` be any best-response
selection. With `c₀ = Λc_s/2`, `c_{A0} = 3Λc_s`, `c_{B0} = 3Ωc_s`,
`r_{A0} = (2/3)(4Λc_s − √(Λc_s(19Λc_s − 6Δc)))`, `r_{B0} = 2Δc²/(9Λc_s)`, `r_{C0} = 2Ω²c_s/Λ`,
the maximizer of `r ↦ C(Λ, r)` over `r ≥ 0` exists, is unique, and equals
`0` if `Δc ≤ c₀`; `r_{A0}` if `c₀ < Δc ≤ c_{A0}`; `r_{B0}` if `c_{A0} < Δc ≤ c_{B0}`;
`r_{C0}` if `c_{B0} < Δc`.

**Formalization Note** Stated as an iff for every `r₀`, which gives both existence and
uniqueness. The radicand of `r_{A0}` is at least `Λ²c_s² > 0` on its branch. -/
theorem normalUse_rebate_closed_form (Ω Λ cs ρ Δc : ℝ) (hΛ : 0 < Λ) (hΛΩ : Λ < Ω)
    (hcs : 0 < cs) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hΔc : 0 < Δc) (s : ℝ → ℝ → ℝ → ℝ)
    (hs : IsBestResponse Ω cs s) (r₀ : ℝ) :
    IsNormalUseOptimal Ω Λ ρ Δc s r₀ ↔
      r₀ = (if Δc ≤ Λ * cs / 2 then 0
        else if Δc ≤ 3 * Λ * cs then
          2 / 3 * (4 * Λ * cs - Real.sqrt (Λ * cs * (19 * Λ * cs - 6 * Δc)))
        else if Δc ≤ 3 * Ω * cs then 2 * Δc ^ 2 / (9 * Λ * cs)
        else 2 * Ω ^ 2 * cs / Λ) := by sorry

end DRBaseline
