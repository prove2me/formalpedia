-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_lemma_10
-- name    : AMPUniversality.Polytope.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:49.676037+00:00
-- url     : https://prove2.me/theorems/6b651860-785a-41da-b254-de289220449b
-- title:
--   Lemma 10, p. 62 — 𝓕_(α,ε) is increasing and convex on [0,1] with 𝓕(1) = 1 and 𝓕(Q) > Q on [0,1)
-- statement:
--   Fix $\varepsilon\in(0,1)$, let $\alpha_*(\varepsilon)>0$ be the minimiser of $G_\varepsilon$ on $[0,\infty)$ (Lemma 8), and let $\alpha\ge\alpha_*(\varepsilon)$. Let $\mathcal F_{\alpha,\varepsilon}:[0,1]\to\mathbb R$ be the correlation map (C.11), with $\mathbb P\{X_\infty=0\}=1-\varepsilon$ and $\mathbb P\{X_\infty\in\{+\infty,-\infty\}\}=\varepsilon$, split in any way between the two signs. Then:
--
--   1. $\mathcal F_{\alpha,\varepsilon}$ is increasing and convex on $[0,1]$;
--   2. $\mathcal F_{\alpha,\varepsilon}(1)=1$;
--   3. if $\alpha>\alpha_*(\varepsilon)$, the left derivative at $1$ satisfies $\mathcal F'_{\alpha,\varepsilon}(1)<1$;
--   4. $$\mathcal F_{\alpha,\varepsilon}(Q)>Q\qquad\text{for all }Q\in[0,1).$$
--
--   The lemma shows that the normalised correlation between consecutive AMP iterates is driven to $1$ by the two-time state evolution, which is used in part (a2) of Lemma 6.
--
--   **Formalization Note** The page asserts $\mathcal F'_{\alpha,\varepsilon}(1)<1$ for every $\alpha\ge\alpha_*$. By (C.15), $\mathcal F'_{\alpha,\varepsilon}(1)=[\varepsilon+2(1-\varepsilon)\Phi(-\alpha)]/G_\varepsilon(\alpha)$, which equals $1$ at $\alpha=\alpha_*$ by (C.6); that clause is therefore stated for $\alpha>\alpha_*$, and the other clauses for $\alpha\ge\alpha_*$. $\alpha_*$ enters as any positive minimiser of $G_\varepsilon$ on $[0,\infty)$, which is unique by Lemma 8. "Increasing" is read as non-decreasing. The derivative at $1$ is taken within $[0,1]$.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 62, Lemma 10 and equation (C.11)

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_StateEvolution

set_option autoImplicit false
open MeasureTheory Set

namespace AMPUniversality.Polytope

/-- Lemma 10, p. 62: for `ε ∈ (0,1)` and `α ≥ α∗(ε)` (the minimiser of `G_ε` on `[0,∞)`),
`𝓕_{α,ε}` is increasing and convex on `[0,1]`, `𝓕_{α,ε}(1) = 1` and `𝓕_{α,ε}(Q) > Q` on
`[0,1)`. The page also asserts `𝓕′_{α,ε}(1) < 1` for every `α ≥ α∗`; at `α = α∗` the
derivative equals `1` by (C.6), so that clause is stated for `α > α∗`. -/
theorem lemma_10 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (αstar : ℝ) (hstar0 : 0 < αstar)
    (hstar : ∀ β : ℝ, 0 ≤ β → GEps ε αstar ≤ GEps ε β)
    (α : ℝ) (hα : αstar ≤ α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ ε) :
    MonotoneOn (lemma10Map ε p α) (Icc 0 1) ∧
    ConvexOn ℝ (Icc 0 1) (lemma10Map ε p α) ∧
    lemma10Map ε p α 1 = 1 ∧
    (αstar < α → ∃ d : ℝ,
      HasDerivWithinAt (lemma10Map ε p α) d (Icc 0 1) 1 ∧ d < 1) ∧
    ∀ Q ∈ Ico (0 : ℝ) 1, Q < lemma10Map ε p α Q := by sorry

end AMPUniversality.Polytope
