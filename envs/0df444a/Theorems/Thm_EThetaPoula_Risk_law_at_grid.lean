-- Prove2me | Theorems.Thm_EThetaPoula_Risk_law_at_grid
-- name    : EThetaPoula.Risk.law_at_grid
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:32.996571+00:00
-- url     : https://prove2.me/theorems/6da7a161-4abd-4e38-b156-831f47a1ff4c
-- title:
--   §6.1, p.23 — the interpolation has the law of e-TH$\varepsilon$O POULA at grid points
-- statement:
--   Let $B$ be a standard Brownian motion independent of $(\theta_0,(X_n)_n)$, and $\bar\theta^\lambda$ the interpolation (39). Then
--   $$
--   \mathcal L(\bar\theta^\lambda_n)=\mathcal L(\theta^\lambda_n),\qquad n\in\mathbb N_0.
--   $$
--
--   This transfers every estimate on the interpolation to the algorithm. The increments of $\sqrt{2\lambda\beta^{-1}}B^\lambda$ over unit intervals have the law of $\sqrt{2\lambda\beta^{-1}}\xi_{n+1}$.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - generalization: stated in the proof section, where Assumptions 1–4 are in force, with the noise of (5) → only the setting of §2.1 is required, for any $(\xi_n)$ with the law and independence of §2.1; reason: the law of the recursion depends only on those; this contains the printed claim
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, after (39), p.23

import Mathlib
import Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
import Definitions.Def_EThetaPoula_Risk_IsInterpolation
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **The interpolation has the algorithm's law at grid points**, Lim, Neufeld, Sabanis, Zhang,
arXiv:2210.13193v3, §6.1, p.23, after (39): `L(θ̄^λ_n) = L(θ^λ_n)` for each `n ∈ ℕ₀`.

**Formalization Note.** `θ̄^λ` is driven by `B` and `θ^λ` by `ξ`; the two are compared in law only,
for any `ξ` with the distribution and independence of `Model.Admissible`, not only for
`ξ_{n+1} := B^λ_{n+1} − B^λ_n`. -/
theorem law_at_grid {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (hS : S.Admissible) (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ≥0 → Ω → Eucl d) (hB : S.IsStandardBrownian B)
    (θb : ℝ≥0 → Ω → Eucl d) (hθb : S.IsInterpolation B lam β ε θb) (n : ℕ) :
    S.P.map (θb n) = S.P.map (S.theta lam β ε n) := by sorry

end EThetaPoula.Risk
