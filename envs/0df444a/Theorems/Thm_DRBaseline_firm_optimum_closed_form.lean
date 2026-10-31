-- Prove2me | Theorems.Thm_DRBaseline_firm_optimum_closed_form
-- name    : DRBaseline.firm_optimum_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:49.182097+00:00
-- url     : https://prove2.me/theorems/e47fb506-7286-414a-99ca-95a35e9702ae
-- title:
--   Closed form of the optimal baseline and rebate $(b^*,r^*)$ and the maximizer set
-- statement:
--   Let $\Omega>0$, $c_s>0$, $\rho\in(0,1]$, $\Delta c>0$ and $s$ any best-response selection. With $c_{A1}=5\Omega c_s/2$, $c_{B1}=4\Omega c_s$, $r_A=2\Delta c/5$, $r_B=2(\Delta c-\Omega c_s)/3$ and $r_C=2\Omega c_s$, the maximizers of $C(b,r)$ over $b,r\ge0$ are:
--
--   1. if $\Delta c\le c_{A1}$: only $\bigl(b,r\bigr)=\bigl(3\Delta c/(5c_s),\,r_A\bigr)$;
--   2. if $c_{A1}<\Delta c<c_{B1}$: only $\bigl(b,r\bigr)=\bigl((7\Omega c_s-\Delta c)/(3c_s),\,r_B\bigr)$;
--   3. if $c_{B1}\le\Delta c$: exactly the pairs with $r\ge2\Omega c_s$ and $rb=2\Omega^2c_s$.
--
--   In every case the least-rebate maximizer is unique; it is the pair of item 1 or 2, and $(b^*,r^*)=(\Omega,r_C)$ when $\Delta c\ge c_{B1}$. Read off these formulas, $r^*$ and $b^*$ increase in $\Delta c$ on the first range, $r^*$ increases and $b^*$ decreases on the second, and both are constant on the third.
--
--   Differences from the source:
--
--   - reading: (b∗, r∗) = arg max C, with r∗ = rC, b∗ = Ω for ∆c ≥ cB1 → the least-rebate maximizer; reason: for Δc ≥ 4Ωc_s the maximizer is not unique: at Ω = c_s = 1, Δc = 5, C(1, 2) = C(1/2, 4) = 3; the page's choice (Ω, 2Ωc_s) has the least rebate
--   - generalization: r∗ = rC and b∗ = Ω for ∆c ≥ cB1 → the whole maximizer set {r ≥ 2Ωc_s, rb = 2Ω²c_s}, which contains (Ω, 2Ωc_s); reason: specializes to the page's pair as the least-rebate maximizer
--   - encoding: ∆c ≤ cA1 and cA1 ≤ ∆c < cB1 → Δc ≤ c_{A1} and c_{A1} < Δc < c_{B1}; reason: the two formulas agree at Δc = c_{A1}
--   - encoding: max_{b,r} C(b, r) → maximum over b ≥ 0, r ≥ 0; reason: the firm's domain
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, pp.OA2–OA3

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsLeastRebateOptimal

namespace DRBaseline

/-- **Closed form of the firm's optimal baseline and rebate `(b∗, r∗)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Lemma 3 and 4, and Propositions 2, 3, and 4, pp.OA2–OA3
("Comparing A and B Cases").

Let `Ω > 0`, `c_s > 0`, `ρ ∈ (0, 1]`, `Δc > 0` and `s` any best-response selection.
With `c_{A1} = 5Ωc_s/2`, `c_{B1} = 4Ωc_s`, `r_A = 2Δc/5`, `r_B = 2(Δc − Ωc_s)/3`, `r_C = 2Ωc_s`:
1. if `Δc ≤ c_{A1}`, the unique maximizer of `C` over `b, r ≥ 0` is `(3Δc/(5c_s), r_A)`;
2. if `c_{A1} < Δc < c_{B1}`, it is `((7Ωc_s − Δc)/(3c_s), r_B)`;
3. if `c_{B1} ≤ Δc`, the maximizers are exactly the `(b, r)` with `r ≥ 2Ωc_s` and `rb = 2Ω²c_s`;
4. for every `Δc > 0`, the least-rebate maximizer is unique and equals the pair of 1 or 2,
   or `(Ω, r_C)` when `Δc ≥ c_{B1}`.

**Formalization Note** For `Δc ≥ 4Ωc_s` the page selects `r∗ = 2Ωc_s`, `b∗ = Ω`; every point
of the ridge `rb = 2Ω²c_s`, `r ≥ 2Ωc_s` gives the same savings `ρΩ(Δc − 2Ωc_s)`, so the
page's pair is the least-rebate maximizer and item 3 lists the whole set. -/
theorem firm_optimum_closed_form (Ω cs ρ Δc : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hΔc : 0 < Δc) (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) :
    (Δc ≤ 5 * Ω * cs / 2 → ∀ b r : ℝ,
      IsFirmOptimal Ω ρ Δc s b r ↔ b = 3 * Δc / (5 * cs) ∧ r = 2 * Δc / 5) ∧
    (5 * Ω * cs / 2 < Δc → Δc < 4 * Ω * cs → ∀ b r : ℝ,
      IsFirmOptimal Ω ρ Δc s b r ↔
        b = (7 * Ω * cs - Δc) / (3 * cs) ∧ r = 2 * (Δc - Ω * cs) / 3) ∧
    (4 * Ω * cs ≤ Δc → ∀ b r : ℝ,
      IsFirmOptimal Ω ρ Δc s b r ↔ 2 * Ω * cs ≤ r ∧ r * b = 2 * Ω ^ 2 * cs) ∧
    (∀ b r : ℝ, IsLeastRebateOptimal Ω ρ Δc s b r ↔
      (b, r) = (if Δc ≤ 5 * Ω * cs / 2 then (3 * Δc / (5 * cs), 2 * Δc / 5)
        else if Δc < 4 * Ω * cs then ((7 * Ω * cs - Δc) / (3 * cs), 2 * (Δc - Ω * cs) / 3)
        else (Ω, 2 * Ω * cs))) := by sorry

end DRBaseline
