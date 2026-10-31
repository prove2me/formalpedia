-- Prove2me | Theorems.Thm_DRBaseline_proposition_3
-- name    : DRBaseline.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:42.092986+00:00
-- url     : https://prove2.me/theorems/68765171-95d8-4e29-92ad-5a50b790c519
-- title:
--   Proposition 3: inflate the baseline and lower the rebate iff $\Delta c>c_B$
-- statement:
--   Let $0<\Lambda<\Omega$, $c_s>0$, $\rho\in(0,1]$, $\Delta c>0$, $c_B(\Lambda,c_s)=5\Lambda c_s/3$, $s$ any best-response selection, $(b^*,r^*)$ the least-rebate maximizer of $C$ and $r_0$ an optimal rebate at the normal-use baseline $b=\Lambda$. Then
--
--   1. if $\Delta c>c_B$: $b^*>\Lambda$ and $r^*<r_0$ (inflate the baseline, lower the rebate);
--   2. if $\Delta c\le c_B$: $b^*\le\Lambda$ and $r^*\ge r_0$ (deflate the baseline, raise the rebate).
--
--   Differences from the source:
--
--   - reading: (b∗, r∗) = arg max C → the least-rebate maximizer; reason: for Δc ≥ 4Ωc_s the maximizer set contains (Λ, r₀) itself (r₀ = 2Ω²c_s/Λ, Λr₀ = 2Ω²c_s), for which 'b∗ > Λ' fails
--   - encoding: r0 = arg max_r C(Λ, r) → every optimal normal-use rebate r₀; reason: r₀ is unique (normalUse_rebate_closed_form)
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Proposition 3, p.17; proof p.OA3

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsLeastRebateOptimal
import Definitions.Def_DRBaseline_IsNormalUseOptimal

namespace DRBaseline

/-- **Proposition 3: inflate the baseline and lower the rebate exactly when `Δc > c_B`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Proposition 3, p.17; proof p.OA3 (`c_B(Λ, c_s) = 5Λc_s/3`).

Let `0 < Λ < Ω`, `c_s > 0`, `ρ ∈ (0, 1]`, `Δc > 0`, `s` any best-response selection,
`(b∗, r∗)` the least-rebate maximizer of `C` and `r₀` an optimal normal-use rebate. Then
1. if `Δc > c_B`: `b∗ > Λ` and `r∗ < r₀`;
2. otherwise: `b∗ ≤ Λ` and `r∗ ≥ r₀`.

**Formalization Note** `(b∗, r∗)` is the least-rebate maximizer (for `Δc ≥ 4Ωc_s` the
maximizer set contains `(Λ, r₀)` itself, for which item 1 fails). -/
theorem proposition_3 (Ω Λ cs ρ Δc : ℝ) (hΛ : 0 < Λ) (hΛΩ : Λ < Ω) (hcs : 0 < cs) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hΔc : 0 < Δc) (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s)
    (b r r₀ : ℝ) (hbr : IsLeastRebateOptimal Ω ρ Δc s b r)
    (hr₀ : IsNormalUseOptimal Ω Λ ρ Δc s r₀) :
    (5 * Λ * cs / 3 < Δc → Λ < b ∧ r < r₀) ∧ (Δc ≤ 5 * Λ * cs / 3 → b ≤ Λ ∧ r₀ ≤ r) := by sorry

end DRBaseline
