-- Prove2me | Theorems.Thm_CompetitionComplexity_proposition_6
-- name    : CompetitionComplexity.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:36.109096+00:00
-- url     : https://prove2.me/theorems/4cc936a9-a160-447c-bf0d-04528ed63630
-- title:
--   Proposition 6 — $y_\varepsilon'''=M_\varepsilon\circ y_\varepsilon$, with the sign and bounds (b)–(e)
-- statement:
--   Let $\varepsilon>0$, let $y_\varepsilon$ be the solution of (15)–(16), and let $\alpha_\varepsilon=y_\varepsilon^{-1}\bigl(\exp(-\tfrac12(1+\sqrt5))\bigr)$. With
--   $$
--   M_\varepsilon(x)=\Bigl(\log x-1-\frac{\varepsilon}{x}\Bigr)\bigl(x\log^2x+x\log x-x-\varepsilon\bigr),
--   $$
--   the following hold.
--
--   1. **(a)** $y_\varepsilon'''(t)=M_\varepsilon(y_\varepsilon(t))$ for every $t\in[0,\phi(\varepsilon))$.
--   2. **(b)** $y_\varepsilon'''(t)\ge0$ for every $t\in[0,\alpha_\varepsilon]$.
--   3. **(c)** If $\varepsilon\le0.25$, then $y_\varepsilon'''(t)\ge-1.173$ for every $t\in[\alpha_\varepsilon,\phi(\varepsilon))$.
--   4. **(d)** If $\varepsilon\le0.25$, there is $x_\varepsilon\in(0.01,0.067)$ such that $y_\varepsilon'''$ is strictly increasing on $[y_\varepsilon^{-1}(x_\varepsilon),\phi(\varepsilon))$.
--   5. **(e)** If $\varepsilon\ge0.25$, then $y_\varepsilon'''(t)\ge0$ for every $t\in[0,\phi(\varepsilon))$.
--
--   These bounds control the Taylor remainder in the comparison of the recursion (9) with the differential equation (Lemma 5(b)).
--
--   **Formalization Note** $y_\varepsilon$ is any solution (unique on $[0,\phi(\varepsilon)]$ by Proposition 5). $y_\varepsilon^{-1}(c)$ is the point $s\in[0,\phi(\varepsilon)]$ with $y_\varepsilon(s)=c$, unique by Proposition 5. $y'''$ is taken within $[0,\phi(\varepsilon)]$, one-sided at $0$. At $t=\phi(\varepsilon)$, where $y_\varepsilon=0$, both $y'''$ and $M_\varepsilon$ are undefined, so the intervals stop before $\phi(\varepsilon)$.
--
--   Differences from the source:
--   - encoding: t ∈ [0, ϕ(ε)] in (a), [αε, ϕ(ε)] in (c), [y⁻¹(xε), ϕ(ε)] in (d), [0, ϕ(ε)] in (e) → the same intervals without the endpoint ϕ(ε); reason: at ϕ(ε), yε = 0 and y‴ and Mε(0) (which contains ε/x) are undefined
--   - encoding: αε = y⁻¹ε(exp(−½(1 + √5))) and y⁻¹ε(xε) → for every α (resp. s) in [0, ϕ(ε)] with y(α) = exp(−(1 + √5)/2) (resp. y(s) = xε); reason: yε is a bijection of [0, ϕ(ε)] onto [0, 1] (Proposition 5), so the point is unique and exists
--   - encoding: y‴ε(t) → iteratedDerivWithin 3 y [0, ϕ(ε)] t; reason: one-sided at t = 0, where y is not defined to the left; the ordinary third derivative inside
--   - reading: y‴ε is increasing in [y⁻¹ε(xε), ϕ(ε)] → strictly increasing; reason: the paper uses "decreasing" for the strictly decreasing yε; Mε is strictly decreasing on (0, xε] in the proof (M′ε < 0 there), so the strict reading is the one the proof gives
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Proposition 6, pp.22–23

import Mathlib
import Definitions.Def_CompetitionComplexity_Phi
import Definitions.Def_CompetitionComplexity_ODE

namespace CompetitionComplexity

/-- **Proposition 6** (the third derivative of `yε`).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Proposition 6, pp.22–23:
"Let ε > 0 and let αε = y−1ε(exp(−½(1 + √5))). Then, the following holds:
(a) For every t ∈ [0,ϕ(ε)] we have y′′′ε(t) = Mε(yε(t)).
(b) For every t ∈ [0,αε] we have y′′′ε(t) ≥ 0.
(c) When ε ≤ 0.25, we have y′′′ε(t) ≥ −1.173 for every t ∈ [αε,ϕ(ε)].
(d) When ε ≤ 0.25, there exists xε ∈ (0.01,0.067) such that y′′′ε is increasing in [y−1ε(xε),ϕ(ε)].
(e) When ε ≥ 0.25, we have y′′′ε(t) ≥ 0 for every t ∈ [0,ϕ(ε)]."

**Formalization Note.** `yε` is any solution `y` of (15)–(16) (unique on `[0, ϕ(ε)]` by Proposition 5).
`y⁻¹(c)` is the point `s ∈ [0, ϕ(ε)]` with `y(s) = c` (unique, by Proposition 5); `αε` and
`y⁻¹(xε)` are quantified that way. `y‴` is `y3` (taken within `[0, ϕ(ε)]`, one-sided at `0`). At
`t = ϕ(ε)` one has `yε = 0`, where `y‴` and `Mε` (which contains `ε/x`) are undefined, so (a), (c),
(d), (e) are stated on intervals that stop before `ϕ(ε)`. "Increasing" in (d) is strictly increasing. -/
theorem proposition_6 (ε : ℝ) (hε : 0 < ε) (y : ℝ → ℝ) (hy : IsSol ε y) :
    (∀ t ∈ Set.Ico 0 (phi ε), y3 ε y t = Meps ε (y t)) ∧
    (∀ α ∈ Set.Icc 0 (phi ε), y α = Real.exp (-(1 + Real.sqrt 5) / 2) →
      ∀ t ∈ Set.Icc 0 α, 0 ≤ y3 ε y t) ∧
    (ε ≤ 0.25 → ∀ α ∈ Set.Icc 0 (phi ε), y α = Real.exp (-(1 + Real.sqrt 5) / 2) →
      ∀ t ∈ Set.Ico α (phi ε), -1.173 ≤ y3 ε y t) ∧
    (ε ≤ 0.25 → ∃ x ∈ Set.Ioo (0.01 : ℝ) 0.067, ∀ s ∈ Set.Icc 0 (phi ε), y s = x →
      StrictMonoOn (y3 ε y) (Set.Ico s (phi ε))) ∧
    (0.25 ≤ ε → ∀ t ∈ Set.Ico 0 (phi ε), 0 ≤ y3 ε y t) := by sorry

end CompetitionComplexity
