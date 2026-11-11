-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_G_11
-- name    : DiffusionErrorAcc.Stability.lemma_G_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:03.949198+00:00
-- url     : https://prove2.me/theorems/cc9adfd6-a5a9-4b2d-8cfa-8879282a4cdf
-- title:
--   Lemma G.11 — Feynman–Kac: f_t(x) = E[f(X_T) | X_t = x] solves ∂_t g + ⟨b, ∇g⟩ + Δg = 0
-- statement:
--   Let $b:\mathbb R^d\times[0,T]\to\mathbb R^d$ be Lipschitz on $\mathbb R^d$ uniformly in $t\in[0,T]$ and jointly continuous, let $(X_t)_{t\in[0,T]}$ follow $dX_t=b(X_t,t)\,dt+\sqrt2\,dW_t$, let $f:\mathbb R^d\to[0,1]$ be uniformly continuous, and let $f_t(x)=\mathbb E[f(X_T)\mid X_t=x]$. Then $g(x,t)=f_t(x)$ satisfies the backward Kolmogorov equation
--   $$\partial_tg+\langle b,\nabla g\rangle+\Delta g=0\qquad\text{on }\mathbb R^d\times(0,T),$$
--   in the classical sense: at every $(x,t)$ with $0<t<T$, $g(x,\cdot)$ is differentiable at $t$, $g(\cdot,t)$ is differentiable near $x$ and twice differentiable at $x$, and the identity holds. It is the bridge between the SDE and the PDE used in the proofs of Lemmas A.1 and A.2.
--
--   **Formalization Note.** $f_t$ is a function `F` with `IsFeynmanKacPosterior b f T F`; $\Delta$ is Mathlib's `Laplacian.laplacian`, $\nabla$ is `gradient`.
--
--   Differences from the source:
--   - reading: g(x, t) := f_t(x) satisfies ∂_t g + ⟨b, ∇g⟩ + Δg = 0 → for every x and t ∈ (0, T): s ↦ F s x differentiable at t, F t differentiable near x, fderiv (F t) differentiable at x, and deriv + ⟨b x t, ∇(F t) x⟩ + Δ(F t) x = 0; reason: a classical solution on ℝ^d × (0, T), the domain on which the paper uses the PDE (p. 22); at t = T the statistic f is only uniformly continuous
--   - encoding: f_t(x) := E[f(X_T) | X_t = x] → a function F with IsFeynmanKacPosterior b f T F: F t x = E[f(X_T)] for every solution X of the SDE started at x at time t, on every probability space (Ω : Type) carrying a standard Brownian motion; reason: the Markov/Feynman–Kac version of the conditional expectation, defined at every x (the paper calls f_t the Feynman–Kac solution); it is unique because the SDE has a unique solution under the Lipschitz hypothesis
--   - encoding: standing assumptions: d ≥ 1, T > 0; f with values in [0, 1] → hypotheses hd : 1 ≤ d, hT : 0 < T, hf; reason: standing assumptions as binders; measurability of f follows from uniform continuity
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 39, Lemma G.11

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE

open MeasureTheory Set Filter
open scoped Topology

namespace DiffusionErrorAcc.Stability

/-- Lemma G.11 (Feynman–Kac, p. 39). Let `b : ℝ^d × [0, T] → ℝ^d` be Lipschitz in space uniformly
in time and jointly continuous, let `f : ℝ^d → [0, 1]` be uniformly continuous, and let
`f_t(x) = E[f(X_T) | X_t = x]` for `dX_t = b(X_t, t) dt + √2 dW_t`. Then `g(x, t) = f_t(x)` is
differentiable in `t`, twice differentiable in `x`, and satisfies
`∂_t g + ⟨b, ∇g⟩ + Δg = 0` on `ℝ^d × (0, T)`. -/
theorem lemma_G_11 {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (b : Rd d → ℝ → Rd d) (hb : IsLipContDrift b T)
    (f : Rd d → ℝ) (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hfu : UniformContinuous f)
    (F : ℝ → Rd d → ℝ) (hF : IsFeynmanKacPosterior b f T F) :
    ∀ x : Rd d, ∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s => F s x) t ∧
      (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (F t) y) ∧
      DifferentiableAt ℝ (fderiv ℝ (F t)) x ∧
      deriv (fun s => F s x) t + inner ℝ (b x t) (gradient (F t) x) +
          Laplacian.laplacian (F t) x = 0 := by sorry

end DiffusionErrorAcc.Stability
