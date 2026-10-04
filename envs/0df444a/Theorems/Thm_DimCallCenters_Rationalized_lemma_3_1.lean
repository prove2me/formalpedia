-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_lemma_3_1
-- name    : DimCallCenters.Rationalized.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:34:47.18007+00:00
-- url     : https://prove2.me/theorems/04b280d0-85df-4b21-b16e-d1d38049f50d
-- title:
--   Lemma 3.1 — the two approximation errors control the continuous cost gap
-- statement:
--   Assume the standing assumptions of Section 2 on $(\mu,D_\lambda)$, and let the staffing cost $F$ be convex and strictly increasing on $(0,\infty)$. For each $\lambda > 0$ let $\hat F_\lambda, \hat\pi_\lambda, \hat G_\lambda$ be real functions and write $\hat C_\lambda(z) = C[z;\hat F_\lambda,\hat\pi_\lambda,\hat G_\lambda]$. Let $x^*_\lambda > 0$ minimize $C_\lambda$ over $(0,\infty)$ (8) and $z^*_\lambda > 0$ minimize $\hat C_\lambda$ over $(0,\infty)$ (9). If, as $\lambda \to \infty$,
--
--   $$\frac{C_\lambda(x^*_\lambda)}{\hat C_\lambda(x^*_\lambda)} \to 1 \quad\text{and}\quad \frac{C_\lambda(z^*_\lambda)}{\hat C_\lambda(z^*_\lambda)} \to 1,$$
--
--   then
--
--   $$\frac{C_\lambda(z^*_\lambda)}{C_\lambda(x^*_\lambda)} \to 1 .$$
--
--   This is the first half of the paper's approximation principle: approximating the cost well at both optima makes the surrogate's optimum nearly optimal for the true continuous cost.
--
--   **Formalization Note** $\lambda$ is real and $\lambda \to \infty$ is `Filter.atTop`; the argmins are hypotheses (any minimizer, ties allowed).
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 13, Lemma 3.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate

open Filter Topology

namespace DimCallCenters.Rationalized

/-- Lemma 3.1 (p. 13). `x lam` is a minimizer `x*_λ` of `C_λ` over `(0, ∞)` (8), `z lam` a
minimizer `z*_λ` over `(0, ∞)` of the surrogate `Ĉ_λ = C[·; F̂_λ, π̂_λ, Ĝ_λ]` (9). If
`C_λ(x*_λ) ≈ Ĉ_λ(x*_λ)` and `C_λ(z*_λ) ≈ Ĉ_λ(z*_λ)` as `λ → ∞`, then
`C_λ(z*_λ) ≈ C_λ(x*_λ)`. -/
theorem lemma_3_1 (M : WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → Clam M F lam (x lam) ≤ Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam ∧
      ∀ z' : ℝ, 0 < z' →
        surrogate (Fh lam) (pih lam) (Gh lam) (z lam) ≤ surrogate (Fh lam) (pih lam) (Gh lam) z')
    (hxapprox : Tendsto (fun lam => Clam M F lam (x lam) /
      surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (𝓝 1))
    (hzapprox : Tendsto (fun lam => Clam M F lam (z lam) /
      surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => Clam M F lam (z lam) / Clam M F lam (x lam)) atTop (𝓝 1) := by sorry

end DimCallCenters.Rationalized
