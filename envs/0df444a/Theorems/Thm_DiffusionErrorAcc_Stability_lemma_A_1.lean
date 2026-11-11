-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_A_1
-- name    : DiffusionErrorAcc.Stability.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:10.035069+00:00
-- url     : https://prove2.me/theorems/0177fbfb-b4d8-482c-bf00-d4883f5d2fa9
-- title:
--   Lemma A.1 — adjoint estimate |E_{q_T} f − E_{q̂_T} f| ≤ ϵ∫_0^T √(E_{q_t}‖∇f_t‖²) dt + (ϵ²/4)T
-- statement:
--   Let $X,\hat X$ solve $dX_t=b(X_t,t)\,dt+\sqrt2\,dW_t$ and $d\hat X_t=\hat b(\hat X_t,t)\,dt+\sqrt2\,dW_t$ on $[0,T]$, driven by the same standard $d$-dimensional Brownian motion $W$, with $X_0=\hat X_0\sim q_0$ independent of $W$; the drifts $b,\hat b:\mathbb R^d\times[0,T]\to\mathbb R^d$ are jointly continuous and Lipschitz in space uniformly in time, and $q_t,\hat q_t$ are the marginal laws. Let $f:\mathbb R^d\to[0,1]$ be a test statistic and $f_t(x)=\mathbb E[f(X_T)\mid X_t=x]$ for the "true" process $X$. If
--   $$\sup_{0<t<T}\mathbb E_{x\sim q_t}\|b(x,t)-\hat b(x,t)\|^2\le\epsilon^2,$$
--   then
--   $$\big|\mathbb E_{q_T}[f]-\mathbb E_{\hat q_T}[f]\big|\le\epsilon\int_0^T\sqrt{\mathbb E_{q_t}\|\nabla f_t\|^2}\,dt+\frac{\epsilon^2}{4}T.$$
--   This is the paper's version of the adjoint method: the error accumulated by a drift perturbation is weighted by the Dirichlet energies of the posterior statistics, which is what later lets those energies decay.
--
--   **Formalization Note.** Expectations of nonnegative quantities and the time integral are lower Lebesgue integrals in `ℝ≥0∞`; the square root is `x ^ (1/2 : ℝ)`.
--
--   Differences from the source:
--   - encoding: dX_t = b(X_t, t)dt + √2 dW_t on [0, T] with a standard d-dimensional Brownian motion W → IsSDESolution: measurable X_u, a.s. continuous paths on [0, T] and X_u = X_0 + ∫_0^u b(X_s, s) ds + √2 W_u for all u ∈ [0, T]; W satisfies the platform predicate EthierKurtz.IsStandardBrownian (time ℝ≥0, every path continuous); X_0 independent of W; reason: the noise is additive, so the pathwise integral equation is the SDE; the law of the solution does not depend on the version of W
--   - encoding: f_t(x) := E[f(X_T) | X_t = x] → a function F with IsFeynmanKacPosterior b f T F: F t x = E[f(X_T)] for every solution X of the SDE started at x at time t, on every probability space (Ω : Type) carrying a standard Brownian motion; reason: the Markov/Feynman–Kac version of the conditional expectation, defined at every x (the paper calls f_t the Feynman–Kac solution); it is unique because the SDE has a unique solution under the Lipschitz hypothesis
--   - encoding: §2.3 implicit regularity: q_0 has a positive C¹ density; the test statistic f is uniformly continuous and C²; d ≥ 1 → explicit hypotheses hq0 (IsRegDensity q0, Law(X_0) = q0 dx), hfu, hf2, hd; reason: standing assumptions of the paper written as binders; measurability and square-integrability of f follow from uniform continuity and 0 ≤ f ≤ 1
--   - encoding: (A.1): sup over 0 < t < T of E_{q_t}‖b(·, t) − b̂(·, t)‖² ≤ ϵ², ϵ a real number → ϵ ≥ 0 and, for every t ∈ (0, T), ∫⁻ ‖b(X_t, t) − b̂(X_t, t)‖² dP ≤ ϵ²; reason: a supremum bounded by ϵ² is a bound at every t
--   - encoding: the right-hand side ϵ∫_0^T √(E_{q_t}‖∇f_t‖²) dt in [0, ∞] read with real arithmetic → computed in ℝ≥0∞ (lintegral, ENNReal.ofReal, x ^ (1/2) for the square root); reason: the energies may be +∞; ℝ≥0∞ avoids the Bochner-integral default value 0 on non-integrable functions
--   - reading: ϵ · ∫_0^T √(E_{q_t}‖∇f_t‖²) dt when ϵ = 0 and the integral is +∞ (0 · ∞, not defined by the source) → 0 (the ℝ≥0∞ convention 0 · ∞ = 0); reason: the only reading under which the printed bound is a statement in that corner
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 21, Lemma A.1 (setting of Appendix A, p. 21)

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DiffusionErrorAcc.Stability

/-- Lemma A.1 (adjoint estimate, p. 21). Two SDEs `dX = b(X, t) dt + √2 dW` and
`dX̂ = b̂(X̂, t) dt + √2 dW` on `[0, T]`, driven by the same standard Brownian motion `W`, with
`X_0 = X̂_0 ∼ q_0` independent of `W` (`q_0` with a positive `C¹` density), drifts jointly
continuous and Lipschitz in space uniformly in time; `f : ℝ^d → [0, 1]` a test statistic and
`f_t(x) = E[f(X_T) | X_t = x]`. If `sup_{0<t<T} E_{q_t} ‖b(·, t) − b̂(·, t)‖² ≤ ϵ²`, then
`|E_{q_T} f − E_{q̂_T} f| ≤ ϵ ∫_0^T √(E_{q_t} ‖∇f_t‖²) dt + (ϵ²/4) T`. -/
theorem lemma_A_1 {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (b bHat : Rd d → ℝ → Rd d) (hb : IsLipContDrift b T) (hbHat : IsLipContDrift bHat T)
    (f : Rd d → ℝ) (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hfu : UniformContinuous f)
    (hf2 : ContDiff ℝ 2 f)
    (F : ℝ → Rd d → ℝ) (hF : IsFeynmanKacPosterior b f T F)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Rd d) (hW : EthierKurtz.IsStandardBrownian P W)
    (X XHat : ℝ → Ω → Rd d) (hX : IsSDESolution P b W T X)
    (hXHat : IsSDESolution P bHat W T XHat) (h0 : ∀ ω, XHat 0 ω = X 0 ω)
    (q0 : Rd d → ℝ) (hq0 : IsRegDensity q0) (hlaw : P.map (X 0) = densMeasure q0)
    (hind : IndepFun (X 0) (fun ω t => W t ω) P)
    (ϵ : ℝ) (hϵ : 0 ≤ ϵ)
    (hA1 : ∀ t ∈ Ioo (0 : ℝ) T,
      ∫⁻ ω, ‖b (X t ω) t - bHat (X t ω) t‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (ϵ ^ 2)) :
    ENNReal.ofReal |(∫ ω, f (X T ω) ∂P) - ∫ ω, f (XHat T ω) ∂P| ≤
      ENNReal.ofReal ϵ *
          ∫⁻ t in Ioo (0 : ℝ) T, (∫⁻ ω, ‖gradient (F t) (X t ω)‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (ϵ ^ 2 / 4 * T) := by sorry

end DiffusionErrorAcc.Stability
