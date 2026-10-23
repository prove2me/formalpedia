-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_lemma_4_18
-- name    : BinaryExtForm.HypercubeRank.lemma_4_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:29.725246+00:00
-- url     : https://prove2.me/theorems/f7ca0c7b-6ee9-4e6f-8584-30a0b213fd63
-- title:
--   Lemma 4.18, p. 13 — rk_B counts the types i whose cut δ(V^i_0) meets some δ(V_{α_j})
-- statement:
--   Let $B$ be a $d$-hypercube binarization with hypercube graph $G(B)$, let $\alpha_1, \dots, \alpha_\ell \in \{0, \dots, 2^d - 2\}$ and choose $\alpha_j < \bar x^j < \alpha_j + 1$. Then
--   $$\operatorname{rk}_B(\alpha_1, \dots, \alpha_\ell) = \Big|\Big\{i : \delta(V^i_0) \cap \bigcup_{j=1}^\ell \delta(V_{\alpha_j}) \ne \emptyset\Big\}\Big|,$$
--   where $V^i_0$ is the set of vertices with $y_i = 0$, $V_\alpha$ the set of vertices with $x \le \alpha$, and $\delta(U)$ the cut of $G(B)$ (edges with exactly one end in $U$).
--
--   So the rank of a hypercube binarization counts the coordinate directions $i$ in which some edge of the hypercube graph crosses one of the levels $\alpha_j$.
--
--   **Formalization Note.** The set on the right is `{i : Fin d | typeHit B α i}`: there are vertices $u, v$ of $B$ whose $y$-parts differ exactly in component $i$, with $x^u \le \alpha_j$ and $x^v \ge \alpha_j + 1$ for some $j$. The range $\alpha_j \in \{0,\dots,2^d-2\}$ is written $\alpha_j + 2 \le 2^d$, avoiding natural-number subtraction. The rank is stated for the chosen points $\bar x^j$ (Definition 4.7). Components are indexed from $0$.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 13, Lemma 4.18

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem lemma_4_18 {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d)
    (xbar : Fin ℓ → ℝ) (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1) :
    rk B xbar = Set.ncard {i : Fin d | typeHit B α i} := by sorry
end BinaryExtForm.HypercubeRank
