-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_lemma_7
-- name    : AMPUniversality.Polytope.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:34.61897+00:00
-- url     : https://prove2.me/theorems/5b353186-aaeb-4898-8c36-3410edd9369e
-- title:
--   Lemma 7, p. 60 — σ² ↦ F(σ², ασ) is monotone and concave, with slope (1/δ)G_ε(α) at 0
-- statement:
--   Let $p_X$ be a probability measure on $\mathbb R$ with $p_X(\{0\})=1-\varepsilon$, let $\delta>0$, and let $\mathsf F(\sigma^2,\theta)=\delta^{-1}\mathbb E\{[\eta(X+\sigma Z;\theta)-X]^2\}$ be the state-evolution map (C.1), with $X\sim p_X$ and $Z\sim\mathsf N(0,1)$ independent and $\eta$ soft thresholding.
--
--   For every $\alpha>0$, the map $\sigma^2\mapsto\mathsf F(\sigma^2,\alpha\sigma)$ is monotone increasing and concave on $[0,\infty)$, $\mathsf F(0,0)=0$, and
--
--   $$\frac{\mathrm d}{\mathrm d(\sigma^2)}\mathsf F(\sigma^2,\alpha\sigma)\Big|_{\sigma=0}=\frac1\delta\Big\{\varepsilon(1+\alpha^2)+2(1-\varepsilon)\,\mathbb E[(Z-\alpha)_+^2]\Big\}.$$
--
--   The slope at the origin is $G_\varepsilon(\alpha)/\delta$; comparing it with $1$ decides whether the state evolution $\sigma^2_{t+1}=\mathsf F(\sigma_t^2,\alpha\sigma_t)$ contracts to $0$, which is how the phase boundary enters the analysis. The result is cited from Donoho, Maleki and Montanari.
--
--   **Formalization Note** "Monotone increasing" is read as non-decreasing. The derivative at $\sigma^2=0$ is the right derivative, since the map is considered on $[0,\infty)$. No moment assumption on $p_X$ is needed for the expectation to be finite, because $|\eta(x+\sigma z;\theta)-x|\le\sigma|z|+\theta$; the page states none.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 60, Lemma 7 and equations (C.1)–(C.2)

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_StateEvolution

set_option autoImplicit false
open MeasureTheory Set

namespace AMPUniversality.Polytope

/-- Lemma 7, p. 60 (cited from [14]): for `α > 0`, `σ² ↦ F(σ², ασ)` is monotone increasing
and concave on `σ² ≥ 0`, `F(0,0) = 0`, and its right derivative at `σ² = 0` is
`(1/δ){ε(1 + α²) + 2(1 − ε)E[(Z − α)₊²]}`, where `p_X({0}) = 1 − ε`. -/
theorem lemma_7 (pX : Measure ℝ) [IsProbabilityMeasure pX]
    (ε δ : ℝ) (hε : (pX {0}).toReal = 1 - ε) (hδ : 0 < δ)
    (α : ℝ) (hα : 0 < α) :
    MonotoneOn (fun s => seMap pX δ s (α * Real.sqrt s)) (Ici 0) ∧
    ConcaveOn ℝ (Ici 0) (fun s => seMap pX δ s (α * Real.sqrt s)) ∧
    seMap pX δ 0 0 = 0 ∧
    HasDerivWithinAt (fun s => seMap pX δ s (α * Real.sqrt s))
      ((1 / δ) * (ε * (1 + α ^ 2) + 2 * (1 - ε) *
        ∫ z : ℝ, (max (z - α) 0) ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1)))
      (Ici 0) 0 := by sorry

end AMPUniversality.Polytope
