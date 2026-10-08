-- Prove2me | Theorems.Thm_BollobasChromatic_Main_theorem_2
-- name    : BollobasChromatic.Main.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:07:43.646827+00:00
-- url     : https://prove2.me/theorems/72a6ff0f-bdfe-4cf8-a539-9a92f0489a9e
-- title:
--   Theorem 2, p. 51 — if E(n,r) = n^α = o(n²/(log n)⁴), α ≥ 1/2, then P(Y_r ≤ (1−c)n^α) ≤ exp{−(c²+o(1))n^{2α−2}}
-- statement:
--   Let $0<p<1$ be fixed. Let $r=r(n)$ and $\alpha=\alpha(n)$ be such that, for all large $n$, $r\ge 3$, $\alpha\ge 1/2$ and
--   $$E(n,r)=\binom nr p^{\binom r2}=n^\alpha ,$$
--   and such that $n^\alpha=o\bigl(n^2/(\log n)^4\bigr)$. Let $Y_r$ be the number of complete $r$-graphs in $G_p=G_{n,p}$. Then for every $0<c\le 1$,
--   $$
--   \mathbb P\bigl(Y_r\le (1-c)n^\alpha\bigr)\le \exp\bigl\{-(c^2+o(1))\,n^{2\alpha-2}\bigr\}.
--   $$
--
--   The number of $r$-cliques is thus exponentially unlikely to fall a constant factor below its mean. Applied to every $n'$-subset of vertices this gives Corollary 3, the input of the chromatic-number bound.
--
--   **Formalization Note** The theorem as printed reads $\exp\{-(c^2+o(1)n^{2\alpha-2})\}$, with a misplaced parenthesis; the last display of the proof (p. 52) gives $\exp\{-(c^2+o(1))n^{2\alpha-2}\}$, which is what is stated. The $o(1)$ is an explicit sequence $\varepsilon_n\to0$ chosen after $p$, $r$, $\alpha$ and $c$, with the bound holding for all large $n$. The page writes $E(r,n)$ for $E(n,r)$. The hypotheses on $r$ and $\alpha$ are required only for all large $n$, and $p$ is fixed (the standing assumption of §1).
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 51, Theorem 2 (bound as in the last display of the proof, p. 52)

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics
open scoped Classical

theorem theorem_2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (r : ℕ → ℕ) (α : ℕ → ℝ)
    (hr : ∀ᶠ n : ℕ in atTop, 3 ≤ r n)
    (hα : ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ α n ∧ expCliques n p (r n) = (n : ℝ) ^ α n)
    (hsmall : (fun n : ℕ => (n : ℝ) ^ α n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 / Real.log (n : ℝ) ^ 4))
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        gnpProb n p (fun G => ((G.cliqueFinset (r n)).card : ℝ) ≤ (1 - c) * (n : ℝ) ^ α n) ≤
          Real.exp (-((c ^ 2 + ε n) * (n : ℝ) ^ (2 * α n - 2))) := by sorry

end BollobasChromatic.Main
