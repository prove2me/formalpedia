-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_A_2
-- name    : DiffusionErrorAcc.Stability.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:14.340029+00:00
-- url     : https://prove2.me/theorems/cd9f8479-adfa-455f-bc71-8fe3c9f5573b
-- title:
--   Lemma A.2 — posterior variance identity d/dt Var_{q_t}(f_t) = 2E_{q_t}‖∇f_t‖²
-- statement:
--   In the setting of Appendix A — $X$ solves $dX_t=b(X_t,t)\,dt+\sqrt2\,dW_t$ on $[0,T]$ with $b$ jointly continuous and Lipschitz in space uniformly in time, $X_0\sim q_0$ independent of the standard Brownian motion $W$, $q_t=\mathrm{Law}(X_t)$, $f:\mathbb R^d\to[0,1]$ a test statistic and $f_t(x)=\mathbb E[f(X_T)\mid X_t=x]$ — for all $0<t<T$ the Dirichlet energy $\mathbb E_{q_t}\|\nabla f_t\|^2$ is finite and
--   $$\frac{d}{dt}\mathrm{Var}_{q_t}(f_t)=2\,\mathbb E_{q_t}\|\nabla f_t\|^2 .$$
--   The variance of the posterior statistic grows at exactly twice its Dirichlet energy; in the reversed time of Appendix B this is (B.1), the decay identity behind Lemmas B.4 and B.5.
--
--   **Formalization Note.** $\mathrm{Var}_{q_t}(f_t)$ is Mathlib's `variance (fun ω => F t (X t ω)) P`; the derivative is `HasDerivAt` at $t$.
--
--   Differences from the source:
--   - encoding: dX_t = b(X_t, t)dt + √2 dW_t on [0, T] with a standard d-dimensional Brownian motion W → IsSDESolution: measurable X_u, a.s. continuous paths on [0, T] and X_u = X_0 + ∫_0^u b(X_s, s) ds + √2 W_u for all u ∈ [0, T]; W satisfies the platform predicate EthierKurtz.IsStandardBrownian (time ℝ≥0, every path continuous); X_0 independent of W; reason: the noise is additive, so the pathwise integral equation is the SDE; the law of the solution does not depend on the version of W
--   - encoding: f_t(x) := E[f(X_T) | X_t = x] → a function F with IsFeynmanKacPosterior b f T F: F t x = E[f(X_T)] for every solution X of the SDE started at x at time t, on every probability space (Ω : Type) carrying a standard Brownian motion; reason: the Markov/Feynman–Kac version of the conditional expectation, defined at every x (the paper calls f_t the Feynman–Kac solution); it is unique because the SDE has a unique solution under the Lipschitz hypothesis
--   - encoding: §2.3 implicit regularity: q_0 has a positive C¹ density; the test statistic f is uniformly continuous and C²; d ≥ 1 → explicit hypotheses hq0 (IsRegDensity q0, Law(X_0) = q0 dx), hfu, hf2, hd; reason: standing assumptions of the paper written as binders; measurability and square-integrability of f follow from uniform continuity and 0 ≤ f ≤ 1
--   - encoding: 'in the setting of the previous lemma' (which also has the second SDE X̂ with drift b̂, and (A.1) as Lemma A.1's own hypothesis) → only the true SDE X, its drift b, q_0 and f; reason: X̂, b̂ and (A.1) do not occur in the statement; the setting with b̂ = b, X̂ = X is always available, so no instance changes
--   - reading: d/dt Var_{q_t}(f_t) = 2E_{q_t}‖∇f_t‖² → E_{q_t}‖∇f_t‖² is finite (Integrable) and t ↦ Var_{q_t}(f_t) has derivative 2E_{q_t}‖∇f_t‖² at t (HasDerivAt); reason: the identity asserts a real derivative at every t ∈ (0, T)
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 22, Lemma A.2, (A.6)

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DiffusionErrorAcc.Stability

/-- Lemma A.2 (posterior variance identity, p. 22). In the setting of Appendix A (the "true" SDE
`dX = b(X, t) dt + √2 dW` on `[0, T]`, `X_0 ∼ q_0` independent of `W`, `f : ℝ^d → [0, 1]` a test
statistic, `f_t(x) = E[f(X_T) | X_t = x]`), for all `0 < t < T`, `E_{q_t} ‖∇f_t‖² < ∞` and
`d/dt Var_{q_t}(f_t) = 2 E_{q_t} ‖∇f_t‖²`. -/
theorem lemma_A_2 {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (b : Rd d → ℝ → Rd d) (hb : IsLipContDrift b T)
    (f : Rd d → ℝ) (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hfu : UniformContinuous f)
    (hf2 : ContDiff ℝ 2 f)
    (F : ℝ → Rd d → ℝ) (hF : IsFeynmanKacPosterior b f T F)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Rd d) (hW : EthierKurtz.IsStandardBrownian P W)
    (X : ℝ → Ω → Rd d) (hX : IsSDESolution P b W T X)
    (q0 : Rd d → ℝ) (hq0 : IsRegDensity q0) (hlaw : P.map (X 0) = densMeasure q0)
    (hind : IndepFun (X 0) (fun ω t => W t ω) P) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      Integrable (fun ω => ‖gradient (F t) (X t ω)‖ ^ 2) P ∧
      HasDerivAt (fun s => variance (fun ω => F s (X s ω)) P)
        (2 * ∫ ω, ‖gradient (F t) (X t ω)‖ ^ 2 ∂P) t := by sorry

end DiffusionErrorAcc.Stability
