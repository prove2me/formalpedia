-- Prove2me | Theorems.Thm_BollobasChromatic_Main_display_9
-- name    : BollobasChromatic.Main.display_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:07:44.995444+00:00
-- url     : https://prove2.me/theorems/c6d704d7-85f1-44ca-aae4-3ce5d8dd330a
-- title:
--   (9), p. 52 — under the hypotheses of Theorem 2, E(X') ≥ (1+o(1))n^α
-- statement:
--   Let $0<p<1$ be fixed. Let $r=r(n)$ and $\alpha=\alpha(n)$ be such that, for all large $n$, $r\ge 3$, $\alpha\ge 1/2$ and $E(n,r)=\binom nr p^{\binom r2}=n^\alpha$, and such that $n^\alpha=o\bigl(n^2/(\log n)^4\bigr)$. Let $X'$ be the number of $K^r$ subgraphs of $G_{n,p}$ sharing no edge with another $K^r$. Then
--   $$
--   \mathbb E(X')\ge (1+o(1))\,n^\alpha .
--   $$
--
--   Since $X'\le X$, this lower bound on $\mathbb E(X)$ is what, combined with (5), proves Theorem 2.
--
--   **Formalization Note** The $o(1)$ is an explicit sequence $\varepsilon_n\to 0$, chosen after $p$, $r$ and $\alpha$, with the inequality holding for all large $n$. The hypotheses on $r$ and $\alpha$ are required only for all large $n$: $E(n,r)=n^\alpha$ cannot hold at $n=1$ when $r\ge 3$.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 52, proof of Theorem 2, display (9)

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem display_9 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (r : ℕ → ℕ) (α : ℕ → ℝ)
    (hr : ∀ᶠ n : ℕ in atTop, 3 ≤ r n)
    (hα : ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ α n ∧ expCliques n p (r n) = (n : ℝ) ^ α n)
    (hsmall : (fun n : ℕ => (n : ℝ) ^ α n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 / Real.log (n : ℝ) ^ 4)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, (1 + ε n) * (n : ℝ) ^ α n ≤
        gnpExp n p (fun G => (isolatedCliqueCount G (r n) : ℝ)) := by sorry

end BollobasChromatic.Main
