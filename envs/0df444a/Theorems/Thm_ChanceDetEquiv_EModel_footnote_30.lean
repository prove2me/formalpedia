-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_footnote_30
-- name    : ChanceDetEquiv.EModel.footnote_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:07.530983+00:00
-- url     : https://prove2.me/theorems/eebdd17f-7ea5-4685-b08d-973518f3d518
-- title:
--   Footnote ‡ to (30) — σ_i²(D) − μ_i²(D) = E[b̂_i − a_i′Db̂]²
-- statement:
--   Let every component $b_k$ be square integrable. With
--   $$\sigma_i^2(D)=E(a_i'Db-b_i)^2,\qquad \mu_i^2(D)=(\mu_{b_i}-a_i'D\mu_b)^2$$
--   as in (30), for every decision rule $D$ and every row $i$,
--   $$\sigma_i^2(D)-\mu_i^2(D)=E[\hat b_i-a_i'D\hat b]^2 .$$
--
--   This identity is what turns (28d), stated with the variance of $a_i'Db-b_i$, into the second constraint of (29), stated with the raw second moment $\sigma_i^2(D)$ and the squared mean slack $\mu_i^2(D)$.
--
--   **Formalization Note** The footnote's display labels the variance $E[a_i'D\hat b-\hat b_i]^2$ as $\sigma_i^2(D)$, while (30) defines $\sigma_i^2(D)$ as the raw second moment. The Lean follows (30), the only reading under which (29) is equivalent to (28c)–(28d), and states the identity the footnote's "derivation" needs.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), p. 28, Eq. (30) and its footnote ‡

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **Footnote ‡ to (30)**, p. 28: if every `b_k` is square integrable, then for every `D` and `i`,
`σ_i²(D) − μ_i²(D) = E[b̂_i − a_i'Db̂]²`, with `σ_i²(D) = E(a_i'Db − b_i)²` and
`μ_i²(D) = (μ_{b_i} − a_i'Dμ_b)²` as in (30). -/
theorem footnote_30 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) :
    sigmaSq P A b D i - (muRow P A b D i) ^ 2 = centeredSecondMoment P A b D i := by sorry

end ChanceDetEquiv.EModel
