-- Prove2me | Theorems.Thm_AnytimeAdaVR_theorem_2
-- name    : AnytimeAdaVR.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:38:34.65905+00:00
-- url     : https://prove2.me/theorems/71d70788-9812-4b95-99ca-1be843036b85
-- title:
--   Theorem 2 — the continuing anytime algorithm has $C P^{5/2}T^{-1/4}$, $C P_{\mathrm{av}}^{5/2}T^{-1/3}$, $C P_0T^{-1/2}$ at every budget
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $f:\mathbb R^d\to\mathbb R$ and a stochastic gradient oracle $g(x;\xi)$, $\xi\sim\mu$, satisfy Assumption 1 (with $L>0$, $\Delta_f\ge0$ and initial point $x_{\mathrm{init}}$) and Assumption 2 (with $\sigma\ge0$). For every deterministic integer query budget $T\ge1$, Algorithm 4 returns one point $\hat x^{\mathrm{lin}}_T$ which satisfies, with $P=1+\Delta_f+L^2+\sigma^2$, $P_0=1+\Delta_f+L^2$ and $P_{\mathrm{av}}=P+\bar L^2$,
--   $$
--   \mathbb E\,\|\nabla f(\hat x^{\mathrm{lin}}_T)\|\le C\begin{cases}
--   P^{5/2}\,T^{-1/4}, & \text{under the basic assumptions},\\
--   P_{\mathrm{av}}^{5/2}\,T^{-1/3}, & \text{under average smoothness with constant }\bar L,\\
--   P_0\,T^{-1/2}, & \text{for noiseless gradients}.
--   \end{cases}
--   $$
--   The algorithm receives only $x_{\mathrm{init}}$: not $L$, $\bar L$, $\sigma$, $\Delta_f$, the budget or the applicable condition. All initialization and validation queries count toward $T$, and the guarantee holds at every budget, including interruptions inside a round or an M pair.
--
--   This is the paper's main result: one continuing algorithm, whose optimization paths are never restarted, attains the optimal rate exponents of all three oracle regimes simultaneously.
--
--   **Formalization Note** $C$ is quantified before every other object. The sample space is a measurable space in `Type`, and $g$ is jointly measurable. Algorithm 4 is `AnytimeAdaVR.xhat`, defined from the three paths, their reservoirs, the dyadic checkpoints, linear validation and the round schedule; it depends only on $g$, $x_{\mathrm{init}}$, $T$ and the random tape.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: each path, its reservoir, and validation use independent random streams → expectations over tapeMeasure μ: the product of i.i.d. optimization samples of law μ per path, i.i.d. uniform coins per path, and i.i.d. validation samples of law μ indexed by (path, checkpoint exponent, index); reason: the probability model of p.10; same law of every quantity the algorithm uses
--   - encoding: noiseless oracle: g(x; ξ) = ∇f(x) almost surely → Noiseless f g μ: for every x, g x ξ = ∇f(x) for μ-a.e. ξ; reason: fresh samples at every query make this the paper's almost-sure exactness at adaptive points; same instances
--   - encoding: Algorithm 4 interrupted after T total queries → xhat g xinit T: the last point published at a round end with global query count ≤ T (xinit before the first publication), the round counts computed from the schedule; reason: publication happens only at round ends and an interruption returns the last published point (Algorithm 4, line 13; pp.10, 26); same output at every budget
--   - encoding: a sample space for ξ → a measurable space Ξ : Type (universe 0); reason: every sample space of the paper is a set; keeps the universal constant's quantifier simple
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.3, Theorem 2, eq. (14), p.10

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_AvgSmooth
import Definitions.Def_AnytimeAdaVR_Noiseless
import Definitions.Def_AnytimeAdaVR_tapeMeasure
import Definitions.Def_AnytimeAdaVR_xhat

namespace AnytimeAdaVR

open MeasureTheory

/-- **Theorem 2 (anytime guarantee in three regimes).** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.3, p.10, eq. (14): "Suppose
Assumptions 1 and 2 hold. For every deterministic integer query budget T ≥ 1, Algorithm 4 returns the
same point x̂^lin_T for all the following guarantees. Set P = 1 + ∆f + L² + σ², P_0 = 1 + ∆f + L², and
P_av = P + L̄² when average smoothness holds. For a universal constant C,
E‖∇f(x̂^lin_T)‖ ≤ C·P^{5/2}T^{−1/4} under the basic assumptions, C·P_av^{5/2}T^{−1/3} under average
smoothness, C·P_0T^{−1/2} for noiseless gradients. The algorithm receives only xinit. All
initialization and validation queries count toward T."

There is one `C > 0` such that for every dimension `d`, sample space `(Ξ, μ)`, objective `f`,
stochastic gradient `g`, initial point `xinit` and constants `L, ∆f, σ` satisfying Assumptions 1
and 2, and every budget `T ≥ 1`, the output `x̂_T = xhat g xinit T` of Algorithm 4 satisfies all three
bounds: the basic one; the average-smooth one for every `L̄` with Assumption 3; and the noiseless one.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. Algorithm 4 is `AnytimeAdaVR.xhat`: the
S, M, D paths on independent streams of the tape, reservoir reports, dyadic checkpoints with linear
validation, publication at round ends, and the last published point at every global query count
`T` (validation queries included). It depends only on `g`, `xinit`, `T` and the tape. Expectations
are lower integrals over `tapeMeasure μ`. `C` is chosen before every other object. The sample space
lives in `Type`. The stochastic gradient is jointly measurable. -/
theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (f : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
        (xinit : EuclideanSpace ℝ (Fin d)) (L Δf σ : ℝ),
        Measurable (Function.uncurry g) → Assumption1 f L Δf xinit → Assumption2 f g μ σ →
        ∀ T : ℕ, 1 ≤ T →
          (∫⁻ ω, ‖gradient f (xhat g xinit T ω)‖ₑ ∂(tapeMeasure μ) ≤
            ENNReal.ofReal (C * (1 + Δf + L ^ 2 + σ ^ 2) ^ (5 / 2 : ℝ) *
              (T : ℝ) ^ (-(1 / 4 : ℝ)))) ∧
          (∀ Lbar : ℝ, AvgSmooth g μ Lbar →
            ∫⁻ ω, ‖gradient f (xhat g xinit T ω)‖ₑ ∂(tapeMeasure μ) ≤
              ENNReal.ofReal (C * (1 + Δf + L ^ 2 + σ ^ 2 + Lbar ^ 2) ^ (5 / 2 : ℝ) *
                (T : ℝ) ^ (-(1 / 3 : ℝ)))) ∧
          (Noiseless f g μ →
            ∫⁻ ω, ‖gradient f (xhat g xinit T ω)‖ₑ ∂(tapeMeasure μ) ≤
              ENNReal.ofReal (C * (1 + Δf + L ^ 2) * (T : ℝ) ^ (-(1 / 2 : ℝ)))) := by sorry

end AnytimeAdaVR
