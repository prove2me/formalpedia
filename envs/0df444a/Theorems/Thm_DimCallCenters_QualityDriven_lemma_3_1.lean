-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_lemma_3_1
-- name    : DimCallCenters.QualityDriven.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:56:04.494479+00:00
-- url     : https://prove2.me/theorems/025366fb-d59f-416c-a45a-d2f341077ffd
-- title:
--   Lemma 3.1 — the two approximation errors control the continuous cost gap
-- statement:
--   Let $(\mu, D)$ be a waiting model and $F$ a staffing cost function, convex and strictly increasing on $(0,\infty)$. For every $\lambda > 0$ let $\hat F_\lambda, \hat\pi_\lambda, \hat G_\lambda$ be real functions, write $\hat C_\lambda(z) = C[z;\hat F_\lambda,\hat\pi_\lambda,\hat G_\lambda]$, and let
--
--   1. $x^*_\lambda > 0$ minimize $C_\lambda$ over $(0,\infty)$, display (8);
--   2. $z^*_\lambda > 0$ minimize $\hat C_\lambda$ over $(0,\infty)$, display (9).
--
--   If, as $\lambda \to \infty$, $C_\lambda(x^*_\lambda)/\hat C_\lambda(x^*_\lambda) \to 1$ and $C_\lambda(z^*_\lambda)/\hat C_\lambda(z^*_\lambda) \to 1$, then
--
--   $$
--   \lim_{\lambda\to\infty}\frac{C_\lambda(z^*_\lambda)}{C_\lambda(x^*_\lambda)} = 1 .
--   $$
--
--   So the approximate optimum is asymptotically as good as the true continuous optimum whenever the surrogate cost is asymptotically exact at both points.
--
--   **Formalization Note** $\lambda$ ranges over the positive reals and $\lambda \to \infty$ is the `atTop` filter on $\mathbb{R}$; the minimizers are function arguments with minimality hypotheses at every $\lambda > 0$ (ties are allowed).
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 13, Lemma 3.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Lemma 3.1 (p. 13). `x lam` is a minimizer `x*_λ` of `C_λ` over `(0, ∞)` (8), `z lam` a
minimizer `z*_λ` over `(0, ∞)` of the DimCallCenters.Rationalized.surrogate `Ĉ_λ = C[·; F̂_λ, π̂_λ, Ĝ_λ]` (9). If
`C_λ(x*_λ) ≈ Ĉ_λ(x*_λ)` and `C_λ(z*_λ) ≈ Ĉ_λ(z*_λ)` as `λ → ∞`, then
`C_λ(z*_λ) ≈ C_λ(x*_λ)`. -/
theorem lemma_3_1 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → DimCallCenters.Rationalized.Clam M F lam (x lam) ≤ DimCallCenters.Rationalized.Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam ∧
      ∀ z' : ℝ, 0 < z' →
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam) ≤ DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) z')
    (hxapprox : Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (x lam) /
      DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (𝓝 1))
    (hzapprox : Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) /
      DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) / DimCallCenters.Rationalized.Clam M F lam (x lam)) atTop (𝓝 1) := by sorry

end DimCallCenters.QualityDriven
