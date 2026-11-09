-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_three_circle
-- name    : BrickworkPorterThomas.Convergence.three_circle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:15:17.536194+00:00
-- url     : https://prove2.me/theorems/b0744385-124c-49a8-9cb4-de236f464950
-- title:
--   Theorem 4.2 — Hadamard three-circle theorem
-- statement:
--   Let $H$ be analytic on a neighbourhood of the closed annulus $r_1\le|z|\le r_2$, where $0<r_1<r_2$, and let $M(r)=\max_{|z|=r}|H(z)|$. Then $\log M(r)$ is a convex function of $\log r$ on $[r_1,r_2]$: for $r_1\le a\le r\le b\le r_2$ with $a<b$,
--
--   $$
--   M(r)\le M(a)^{\theta}M(b)^{1-\theta},\qquad \theta=\frac{\log(b/r)}{\log(b/a)} .
--   $$
--
--   In particular, for $r_1\le r\le r_2$,
--
--   $$
--   M(r)\le M(r_1)^{\theta}M(r_2)^{1-\theta},\qquad\theta=\frac{\log(r_2/r)}{\log(r_2/r_1)} .
--   $$
--
--   The paper applies it to a Möbius-transformed truncated Laplace transform. A bound near the origin (Lemma A.1) and a bound on a half-plane combine into a bound on the intermediate frequencies of Lemma 4.3.
--
--   **Formalization Note** Convexity of $\log M$ in $\log r$ is stated in its multiplicative form on every subinterval. That form is equivalent to convexity where $M>0$, and it remains meaningful when $M$ vanishes ($\log M=-\infty$), which happens only for $H\equiv0$ on the annulus. "Analytic on a neighbourhood of the annulus" is `AnalyticOnNhd` on the closed annulus.
--
--   Differences from the source:
--
--   - encoding: log M(r) convex as a function of log r → M(r) ≤ M(a)^θ M(b)^{1−θ} with θ = log(b/r)/log(b/a) for all r₁ ≤ a ≤ r ≤ b ≤ r₂, a < b; reason: the multiplicative form of convexity of log M ∘ exp, which also covers M = 0 (log M = −∞)
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §4, p. 11, Theorem 4.2, Eqs. (52)–(53); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Densities

namespace BrickworkPorterThomas.Convergence

/-- Theorem 4.2 (Hadamard three-circle theorem, p. 11). Let `H` be analytic on a neighbourhood of
the closed annulus `r₁ ≤ |z| ≤ r₂`, `0 < r₁ < r₂`, and `M(r) = max_{|z|=r} |H(z)|`.

1. `log M(r)` is convex as a function of `log r` on `[r₁, r₂]`, in the multiplicative form
   `M(r) ≤ M(a)^θ M(b)^{1−θ}`, `θ = log(b/r)/log(b/a)`, for all `r₁ ≤ a ≤ r ≤ b ≤ r₂`, `a < b`
   (this form allows `M` to vanish, i.e. `log M = −∞`).
2. In particular, `M(r) ≤ M(r₁)^θ M(r₂)^{1−θ}` with `θ = log(r₂/r)/log(r₂/r₁)` for `r₁ ≤ r ≤ r₂`. -/
theorem three_circle (H : ℂ → ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hH : AnalyticOnNhd ℂ H {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂}) :
    (∀ a r b : ℝ, r₁ ≤ a → a < b → b ≤ r₂ → a ≤ r → r ≤ b →
      circleMax H r ≤
        circleMax H a ^ (Real.log (b / r) / Real.log (b / a)) *
          circleMax H b ^ (1 - Real.log (b / r) / Real.log (b / a))) ∧
    (∀ r : ℝ, r₁ ≤ r → r ≤ r₂ →
      circleMax H r ≤
        circleMax H r₁ ^ (Real.log (r₂ / r) / Real.log (r₂ / r₁)) *
          circleMax H r₂ ^ (1 - Real.log (r₂ / r) / Real.log (r₂ / r₁))) := by sorry

end BrickworkPorterThomas.Convergence
