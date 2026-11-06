-- Prove2me | Theorems.Thm_AnytimeAdaVR_proposition_E_1
-- name    : AnytimeAdaVR.proposition_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:39:21.644135+00:00
-- url     : https://prove2.me/theorems/4a61e672-a52a-4213-bc51-cc37efcc60d8
-- title:
--   Proposition E.1 — linear validation: (54) at each checkpoint and (56) at every budget
-- statement:
--   Suppose Assumptions 1 and 2 hold and the stochastic gradient is jointly measurable. Run Algorithm 4 (linear validation) from $x_{\mathrm{init}}$.
--
--   1. At every checkpoint $n=2^k$, the published point satisfies
--   $$
--   \mathbb E\|\nabla f(Z^{\mathrm{lin}}_n)\|\le\min_{i\in\{S,M,D\}}\mathbb E\|\nabla f(X_i)\|+\frac{\sqrt6\,\sigma}{\sqrt n},
--   $$
--   where $X_i$ is the report of path $i$ after $n$ local queries.
--   2. For every deterministic integer budget $T\ge1$, define
--   $$
--   B_S(T)=24^{1/4}S\,T^{-1/4},\qquad B_M(T)=24^{1/3}M\,T^{-1/3},\qquad B_D(T)=\sqrt{24}\,D_0\,T^{-1/2},
--   $$
--   with $S=C_{1/4}(L)$, $M=C_{1/3}(\bar L)$, $D_0$ from (50) and $g_0=\sqrt{2L\Delta_f}$. Then the output $\hat x^{\mathrm{lin}}_T$ satisfies $\mathbb E\|\nabla f(\hat x^{\mathrm{lin}}_T)\|\le B_i(T)+(12\sigma+3g_0)/\sqrt T$ for $i=S$ always, for $i=M$ whenever average smoothness holds with constant $\bar L$, and for $i=D$ whenever gradients are noiseless. Equivalently,
--   $$
--   \mathbb E\|\nabla f(\hat x^{\mathrm{lin}}_T)\|\le\min_{i\in I}B_i(T)+\frac{12\sigma+3g_0}{\sqrt T},
--   $$
--   where $I$ contains S always, M under average smoothness and D for exact gradients. The set $I$ is used only to state the bound; the algorithm does not receive it.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: each path, its reservoir, and validation use independent random streams → expectations over tapeMeasure μ: the product of i.i.d. optimization samples of law μ per path, i.i.d. uniform coins per path, and i.i.d. validation samples of law μ indexed by (path, checkpoint exponent, index); reason: the probability model of p.10; same law of every quantity the algorithm uses
--   - encoding: noiseless oracle: g(x; ξ) = ∇f(x) almost surely → Noiseless f g μ: for every x, g x ξ = ∇f(x) for μ-a.e. ξ; reason: fresh samples at every query make this the paper's almost-sure exactness at adaptive points; same instances
--   - encoding: min_{i∈I} B_i(T) + (12σ + 3g_0)/√T, with I determined by the applicable conditions → three bounds B_i(T) + (12σ + 3g_0)/√T, each under the condition that puts i into I; reason: a quantity is at most a minimum plus c iff it is at most each term plus c; same instances
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. E.1, Proposition E.1, eqs. (54)–(56), pp.26–27

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_AvgSmooth
import Definitions.Def_AnytimeAdaVR_Noiseless
import Definitions.Def_AnytimeAdaVR_tapeMeasure
import Definitions.Def_AnytimeAdaVR_xhat
import Definitions.Def_AnytimeAdaVR_coefCgamma
import Definitions.Def_AnytimeAdaVR_coefD0

namespace AnytimeAdaVR

open MeasureTheory

/-- **Proposition E.1 (Linear validation and explicit coefficients).** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. E.1, pp.26–27:
"Under the basic assumptions, at every checkpoint n the published point Z^lin_n satisfies
E‖∇f(Z^lin_n)‖ ≤ min_{i∈{S,M,D}} E‖∇f(X_i)‖ + √6σ/√n. (54) For every deterministic integer query budget
T ≥ 1, define B_S(T) = 24^{1/4} S T^{−1/4}, B_M(T) = 24^{1/3} M T^{−1/3}, B_D(T) = √24 D_0 T^{−1/2}, (55)
where S, M, g_0 are the explicit quantities in Appendix G, and D_0 is given by (50). Let I include S
always, M when average smoothness holds, and D when gradients are exact. The same returned point
x̂^lin_T then satisfies E‖∇f(x̂^lin_T)‖ ≤ min_{i∈I} B_i(T) + (12σ + 3g_0)/√T. (56)"

Under Assumptions 1 and 2, with `S = C_{1/4}(L)`, `M = C_{1/3}(L̄)`, `g_0 = √(2L∆f)`:
1. (54) at every checkpoint `n = 2^k`, with `X_i` the frozen reports after `n` local queries;
2. (56) at every budget `T ≥ 1`: `E‖∇f(x̂_T)‖ ≤ B_S(T) + (12σ + 3g_0)/√T`; for every `L̄` with
   Assumption 3, also `≤ B_M(T) + (12σ + 3g_0)/√T`; and for noiseless gradients, also
   `≤ B_D(T) + (12σ + 3g_0)/√T`.

**Formalization Note.** "`min_{i∈I} B_i(T) + c`" is stated as the three bounds `B_i(T) + c`, one for
each condition that puts `i` into `I` (equivalent to the minimum form). Expectations are lower
integrals over the tape `tapeMeasure μ` (independent optimization, coin and validation streams). The
algorithm (`checkpointPoint`, `xhat`) receives only `xinit`. The stochastic gradient is jointly
measurable. -/
theorem proposition_E_1 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)}
    {xinit : EuclideanSpace ℝ (Fin d)} {L Δf σ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hA1 : Assumption1 f L Δf xinit)
    (hA2 : Assumption2 f g μ σ) :
    (∀ k : ℕ, ∫⁻ ω, ‖gradient f (checkpointPoint g xinit k ω)‖ₑ ∂(tapeMeasure μ) ≤
      (⨅ i : Path, ∫⁻ ω, ‖gradient f (pathReport g xinit i ω (2 ^ k))‖ₑ ∂(tapeMeasure μ)) +
        ENNReal.ofReal (Real.sqrt 6 * σ / Real.sqrt ((2 : ℝ) ^ k))) ∧
    (∀ T : ℕ, 1 ≤ T →
      (∫⁻ ω, ‖gradient f (xhat g xinit T ω)‖ₑ ∂(tapeMeasure μ) ≤
        ENNReal.ofReal ((24 : ℝ) ^ (1 / 4 : ℝ) * coefCgamma (1 / 4) Δf L σ L *
            (T : ℝ) ^ (-(1 / 4 : ℝ)) +
          (12 * σ + 3 * Real.sqrt (2 * L * Δf)) / Real.sqrt T)) ∧
      (∀ Lbar : ℝ, AvgSmooth g μ Lbar →
        ∫⁻ ω, ‖gradient f (xhat g xinit T ω)‖ₑ ∂(tapeMeasure μ) ≤
          ENNReal.ofReal ((24 : ℝ) ^ (1 / 3 : ℝ) * coefCgamma (1 / 3) Δf L σ Lbar *
              (T : ℝ) ^ (-(1 / 3 : ℝ)) +
            (12 * σ + 3 * Real.sqrt (2 * L * Δf)) / Real.sqrt T)) ∧
      (Noiseless f g μ →
        ∫⁻ ω, ‖gradient f (xhat g xinit T ω)‖ₑ ∂(tapeMeasure μ) ≤
          ENNReal.ofReal (Real.sqrt 24 * coefD0 Δf L * (T : ℝ) ^ (-(1 / 2 : ℝ)) +
            (12 * σ + 3 * Real.sqrt (2 * L * Δf)) / Real.sqrt T))) := by sorry

end AnytimeAdaVR
