-- Prove2me | Theorems.Thm_FoundationsML_ModelSelection_convex_surrogate_bound_v2
-- name    : FoundationsML.ModelSelection.convex_surrogate_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:56.890343+00:00
-- url     : https://prove2.me/theorems/8cb91e48-0117-47e0-a750-d63cb39680ef
-- title:
--   Theorem 4.7 — excess-error bound via a convex surrogate loss (measurable, integrable data)
-- statement:
--   **Statement (Theorem 4.7, p. 76, PDF p. 93).** Let $\Phi$ be convex and non-decreasing and $\eta(x)=\Pr[y=+1\mid x]\in[0,1]$. Assume there exist $s\ge1$, $c>0$ with $|h^*(x)|^s = |\eta(x)-\tfrac12|^s \le c^s\big(L_\Phi(x,0)-L_\Phi(x,h^*_\Phi(x))\big)$ for all $x\in X$, where $h^*_\Phi$ is a pointwise minimizer of $u\mapsto L_\Phi(x,u)=\eta(x)\Phi(-u)+(1-\eta(x))\Phi(u)$. Then, for any hypothesis $h:X\to\mathbb R$ with finite $\Phi$-loss,
--   $$R(h) - R^* \le 2c\big(L_\Phi(h)-L^*_\Phi\big)^{1/s}.$$
--
--   **Formalization Note.** The retired version had no measurability or integrability hypothesis, so the Bochner integrals defining $L_\Phi(h)$ and $L^*_\Phi$ could silently be $0$ (disproved with a non-measurable integrand on a two-point space). Now explicit: the book's standing measurability (footnote 2, p. 10) of $\eta$, $h$ and $h^*_\Phi$; $\eta$ valued in $[0,1]$ (it is a conditional probability); and integrability of the two $\Phi$-loss integrands, i.e. finiteness of $L_\Phi(h)$ and $L^*_\Phi$, which the book's expectations presuppose (if $L_\Phi(h)=+\infty$ the bound is trivially true, so nothing is lost). The classification risks $R(h)=\mathbb E[\eta\mathbf 1_{h<0}+(1-\eta)\mathbf 1_{h\ge0}]$ and $R^*=R(h^*)$ are integrals of $[0,1]$-valued measurable functions and need no further hypothesis. As before, `ConvexOn ℝ univ Φ`/`Monotone Φ` are "convex and non-decreasing", $h^*=\eta-\tfrac12$ is `BayesScore`, and the book's extended-valued choices $h^*_\Phi(x)=\pm\infty$ at $\eta(x)\in\{0,1\}$ are outside this real-valued formalization (the theorem applies whenever a real-valued pointwise minimizer is supplied).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 76, Theorem 4.7 (PDF p. 93)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_BayesScore
import Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise
import Definitions.Def_FoundationsML_ModelSelection_ExpectedPhiLoss
import Definitions.Def_FoundationsML_ModelSelection_ScoringRisk

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Theorem 4.7 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 76, PDF p. 93). Let `Φ : ℝ → ℝ` be convex and non-decreasing, `η(x) =
P[y = +1 | x] ∈ [0,1]`, and let `hΦstar` be a pointwise minimizer of the Φ-loss
`u ↦ L_Φ(x, u)` at every `x` (the book's `h*_Φ`, taken real-valued). Assume there exist
`s ≥ 1` and `c > 0` with `|h*(x)|^s ≤ c^s (L_Φ(x,0) − L_Φ(x,h*_Φ(x)))` for all `x`, where
`h*(x) = η(x) − 1/2` is the Bayes scoring function. Then, for any hypothesis `h : X → ℝ`,
`R(h) − R* ≤ 2c (L_Φ(h) − L*_Φ)^{1/s}`.

**Formalization Note.** Replaces `convex_surrogate_bound`, which had no measurability or
integrability hypothesis, so the Bochner integrals defining `L_Φ(h)` could silently be `0`
(disproved with a non-measurable integrand). Now explicit: the book's standing measurability
of `η`, `h` and `h*_Φ` (footnote 2, p. 10), `η` valued in `[0,1]` (it is a conditional
probability), and integrability of the two Φ-loss integrands, i.e. finiteness of `L_Φ(h)` and
`L*_Φ`, which the book's expectations presuppose (if `L_Φ(h) = +∞` the bound is trivially
true and nothing is lost). The classification risks are integrals of `[0,1]`-valued
measurable functions and need no further hypothesis. As in the retired version, the book's
extended-valued choices `h*_Φ(x) = ±∞` at `η(x) ∈ {0,1}` are outside this real-valued
formalization: the theorem applies whenever a real-valued pointwise minimizer is supplied. -/
theorem convex_surrogate_bound_v2 {X : Type*} [MeasurableSpace X] (DX : Measure X)
    [IsProbabilityMeasure DX] (η : X → ℝ) (hη_meas : Measurable η)
    (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (Φ : ℝ → ℝ)
    (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hΦstar : X → ℝ) (hΦstar_meas : Measurable hΦstar)
    (hΦstar_min : ∀ x u, PhiLossPointwise η Φ x (hΦstar x) ≤ PhiLossPointwise η Φ x u)
    (hΦstar_int : Integrable (fun x => PhiLossPointwise η Φ x (hΦstar x)) DX)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hbound : ∀ x, |BayesScore η x| ^ s ≤
      c ^ s * (PhiLossPointwise η Φ x 0 - PhiLossPointwise η Φ x (hΦstar x)))
    (h : X → ℝ) (hh_meas : Measurable h)
    (hh_int : Integrable (fun x => PhiLossPointwise η Φ x (h x)) DX) :
    ScoringRisk DX η h - ScoringRisk DX η (BayesScore η) ≤
      2 * c * (ExpectedPhiLoss DX η Φ h - ExpectedPhiLoss DX η Φ hΦstar) ^ (1 / s) := by sorry

end FoundationsML.ModelSelection
