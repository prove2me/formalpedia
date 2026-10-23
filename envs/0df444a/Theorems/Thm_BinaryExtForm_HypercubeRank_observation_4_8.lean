-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_observation_4_8
-- name    : BinaryExtForm.HypercubeRank.observation_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:28.838496+00:00
-- url     : https://prove2.me/theorems/d4b12e14-e8d5-48d8-8f5b-7a05582a6f83
-- title:
--   Observation 4.8, p. 11 — rk_B is the optimum of the set covering problem on the α_j-edges of sk(B)
-- statement:
--   Let $B \subseteq [0,k] \times [0,1]^d$ be a natural binarization of $x$ in the range $\{0, \dots, k\}$, let $\alpha_1, \dots, \alpha_\ell \in \{0, \dots, k-1\}$ and let $\alpha_j < \bar x^j < \alpha_j + 1$ for $j \in [\ell]$. Then $\operatorname{rk}_B(\alpha_1, \dots, \alpha_\ell) = \operatorname{lpr}(\operatorname{conv}(\bigcup_j B(\bar x^j)))$ is the optimum value of the set covering problem whose constraint rows are the indicator vectors of the $\alpha_j$-edges ($j \in [\ell]$) of the skeleton $\operatorname{sk}(B)$:
--   $$\operatorname{rk}_B(\alpha_1, \dots, \alpha_\ell) = \min\{|Z| : Z \subseteq [d],\ Z \text{ meets the support of the indicator vector of every } \alpha_j\text{-edge}\}.$$
--
--   The rank of a natural binarization therefore depends only on the edge structure of $B$ and on which edges cross the levels $\alpha_j$.
--
--   **Formalization Note.** Only the second sentence of Observation 4.8 is formalized. Its first sentence, identifying $\operatorname{rk}_B$ with the rank of a property of a binary extended formulation satisfying the hypotheses of Theorem 4.6, is not stated, since this mission does not formalize binary extended formulations or Theorem 4.6, and Theorem 4.23 does not use it. The indicator entry $t_i = 1$ is encoded as "not ($y^u_i = y^v_i = 0$ or $y^u_i = y^v_i = 1$)". The rank is stated for the chosen points $\bar x^j$ (Definition 4.7). The hypothesis $B \subseteq [0,k] \times [0,1]^d$ is the paper's.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 11, Observation 4.8 (second sentence); Definition 4.7, α-edge and indicator vector on p. 10

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem observation_4_8 {d k ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B)
    (hN : IsNatural B) (hBk : ∀ p ∈ B, 0 ≤ p 0 ∧ p 0 ≤ k) (α : Fin ℓ → ℕ) (hα : ∀ j, α j < k)
    (xbar : Fin ℓ → ℝ) (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1) :
    rk B xbar = sInf {c : ℕ | ∃ Z : Finset (Fin d), Z.card = c ∧
      ∀ u v, (∃ j, IsAlphaEdge B (α j) u v) → ∃ i ∈ Z, indicator u v i} := by sorry
end BinaryExtForm.HypercubeRank
