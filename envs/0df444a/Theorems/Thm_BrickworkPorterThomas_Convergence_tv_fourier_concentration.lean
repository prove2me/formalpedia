-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_tv_fourier_concentration
-- name    : BrickworkPorterThomas.Convergence.tv_fourier_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:15:32.255641+00:00
-- url     : https://prove2.me/theorems/4359bef0-2587-4074-b457-281139f8dddd
-- title:
--   Theorem 2.8 — total variation bounded by the Fourier $L^2$ distance plus the tail mass
-- statement:
--   Let $f$ and $g$ be probability densities on $\mathbb R$ with characteristic functions $\hat f,\hat g$, and suppose each assigns probability mass at least $1-\delta$ to the interval $[0,L]$. Then
--
--   $$
--   d_{TV}(f,g)\le\left(\frac{L}{8\pi}\int_{-\infty}^{\infty}|\hat f(t)-\hat g(t)|^2\,dt\right)^{1/2}+\delta .
--   $$
--
--   This is a tail-aware version of Bobkov's Fourier bound. It reduces closeness in total variation of distributions that are mostly concentrated on a short interval to an $L^2$ estimate on characteristic functions, and the paper uses it with $L=2k/d$ and $\delta=2^{-k}$.
--
--   **Formalization Note** The Fourier integral is a $[0,\infty]$-valued integral, so the right side may be $+\infty$, and the inequality is stated in $[0,\infty]$. No square-integrability is assumed.
--
--   Differences from the source:
--
--   - encoding: real inequality with ∫|f̂−ĝ|² possibly infinite → inequality in [0,∞] with the [0,∞]-valued integral; reason: an infinite right side is allowed by the source and stays meaningful
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §2.1, p. 7, Theorem 2.8, Eq. (23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Densities

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Theorem 2.8 (p. 7). If `f, g` are probability densities each putting mass at least `1 − δ` on
`[0, L]`, then `d_TV(f, g) ≤ (L/(8π) ∫_ℝ |f̂(t) − ĝ(t)|² dt)^{1/2} + δ`. The integral is a
`[0, ∞]`-valued integral and may be `+∞`. -/
theorem tv_fourier_concentration (f g : ℝ → ℝ) (L δ : ℝ)
    (hf : IsDensity f) (hg : IsDensity g)
    (hfL : 1 - δ ≤ ∫ x in Set.Icc 0 L, f x) (hgL : 1 - δ ≤ ∫ x in Set.Icc 0 L, g x) :
    ENNReal.ofReal (dTV f g) ≤
      (ENNReal.ofReal (L / (8 * Real.pi)) *
          ∫⁻ t, ‖charDensity f t - charDensity g t‖ₑ ^ 2) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal δ := by sorry

end BrickworkPorterThomas.Convergence
