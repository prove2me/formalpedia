-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_theorem_4_23
-- name    : BinaryExtForm.HypercubeRank.theorem_4_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:26.028686+00:00
-- url     : https://prove2.me/theorems/31ecb81b-c9e7-425c-b6bb-8469f92c45e2
-- title:
--   Theorem 4.23, p. 14 — every d-hypercube binarization has rank at least that of the logarithmic binarization
-- statement:
--   Let $B \subseteq \mathbb R \times [0,1]^d$ be a $d$-hypercube binarization (its vertices project bijectively onto $\{0,1\}^d$ and have the $x$-values $0, 1, \dots, 2^d - 1$), let $B^L = B^L(d)$ be the logarithmic binarization $\{(x,y) \in \mathbb R \times [0,1]^d : x = \sum_{i=1}^d 2^{i-1} y_i\}$, and let $\alpha_1, \dots, \alpha_\ell \in \{0, \dots, 2^d - 2\}$. Then
--   $$\operatorname{rk}_B(\alpha_1, \dots, \alpha_\ell) \ge \operatorname{rk}_{B^L}(\alpha_1, \dots, \alpha_\ell).$$
--   Here $\operatorname{rk}_B(\alpha_1,\dots,\alpha_\ell) = \operatorname{lpr}(\operatorname{conv}(\bigcup_j B(\bar x^j)))$ for points $\alpha_j < \bar x^j < \alpha_j + 1$ (Definition 4.7): the least number of convexifications of $y$-variables that removes all points of $B$ with $x$ strictly between $\alpha_j$ and $\alpha_j + 1$.
--
--   Among all binarizations whose vertices form a $d$-dimensional hypercube with distinct integer $x$-values, the logarithmic binarization needs the fewest sequential convexification steps to eliminate any prescribed family of fractional $x$-ranges.
--
--   **Formalization Note.** The fractional points are chosen independently for $B$ (`xbar`) and for $B^L$ (`xbarL`), each with $\alpha_j < \bar x^j < \alpha_j + 1$; the statement holds for every such choice, so no lemma on the independence of $\operatorname{rk}$ from the choice is needed. The range $\{0,\dots,2^d-2\}$ is written $\alpha_j + 2 \le 2^d$. No hypothesis is added to the page's; $\ell = 0$ is allowed.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 14, Theorem 4.23

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem theorem_4_23 {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d)
    (xbar xbarL : Fin ℓ → ℝ)
    (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1)
    (hxL : ∀ j, (α j : ℝ) < xbarL j ∧ xbarL j < α j + 1) :
    rk (BL d) xbarL ≤ rk B xbar := by sorry
end BinaryExtForm.HypercubeRank
