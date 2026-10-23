-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_corollary_4_19
-- name    : BinaryExtForm.HypercubeRank.corollary_4_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:24.677027+00:00
-- url     : https://prove2.me/theorems/4687df92-1823-4f91-ade1-fbb34722b1e7
-- title:
--   Corollary 4.19, p. 13 — rk_B(α_1,…,α_ℓ) = d − f_B(α_1,…,α_ℓ)
-- statement:
--   Let $B$ be a $d$-hypercube binarization with hypercube graph $G(B)$, let $\alpha_1, \dots, \alpha_\ell \in \{0, \dots, 2^d - 2\}$ and choose $\alpha_j < \bar x^j < \alpha_j + 1$. Then
--   $$\operatorname{rk}_B(\alpha_1, \dots, \alpha_\ell) = d - f_B(\alpha_1, \dots, \alpha_\ell),$$
--   where $f_B(\alpha_1, \dots, \alpha_\ell) = |\{i : \delta(V^i_0) \cap \bigcup_{j=1}^\ell \delta(V_{\alpha_j}) = \emptyset\}|$ counts the coordinate directions in which no edge of $G(B)$ crosses any of the levels $\alpha_j$.
--
--   This is the form of Lemma 4.18 used in the proof of Theorem 4.23: comparing ranks of hypercube binarizations reduces to comparing the numbers $f_B$.
--
--   **Formalization Note.** The subtraction is in $\mathbb N$ and is exact, since $f_B \le d$ by construction (it counts a subset of $d$ components). The rank is stated for the chosen points $\bar x^j$; $\alpha_j + 2 \le 2^d$ encodes the range.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 13, Corollary 4.19 (f_B defined just before it on p. 13)

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem corollary_4_19 {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d)
    (xbar : Fin ℓ → ℝ) (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1) :
    rk B xbar = d - fB B α := by sorry
end BinaryExtForm.HypercubeRank
