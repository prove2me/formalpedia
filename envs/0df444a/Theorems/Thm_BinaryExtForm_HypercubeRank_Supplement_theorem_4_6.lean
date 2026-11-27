-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_Supplement_theorem_4_6
-- name    : BinaryExtForm.HypercubeRank.Supplement.theorem_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T04:02:36.054795+00:00
-- url     : https://prove2.me/theorems/1fa04569-c22f-4c53-a738-1b03aff82043
-- title:
--   Theorem 4.6, p. 10 — with natural binarizations, the rank of P^i_{α_1,…,α_ℓ} equals lpr(conv(⋃_j B_i(x̄^j_i))) (corrected: P^i read as x̄_i ≤ α_j or x̄_i ≥ α_j + 1)
-- statement:
--   Let $P \subseteq [0,k]^p \times \mathbb R^{n-p}$ be a polytope, $k$ a positive integer, and let $Q \subseteq \mathbb R^n \times [0,1]^{pd}$ be the binary extended formulation of $P$ with binarizations $B_1, \dots, B_p \subseteq \mathbb R \times [0,1]^d$ of $x_1, \dots, x_p$ in the range $\{0,\dots,k\}$, all of them natural. Let $\alpha_1, \dots, \alpha_\ell \in \mathbb Z$ and $i \in [p]$, and assume that for every $j \in [\ell]$ there is a vertex $(\bar x^j, \bar y^j)$ of $Q$ with $\alpha_j < \bar x^j_i < \alpha_j + 1$. Then the rank of property $\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}$ (Definition 4.1) satisfies
--   $$\operatorname{rank}\big(\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}\big) = \operatorname{lpr}\Big(\operatorname{conv}\Big(\bigcup_{j \in [\ell]} B_i(\bar x^j_i)\Big)\Big),$$
--   where $B_i(f) = \{(x_i,y_i) \in B_i : x_i = f\}$ and the lift-and-project rank is taken with respect to the variables $y_{i1}, \dots, y_{id}$.
--
--   The theorem shows that, for natural binarizations, the number of convexification steps needed to cut off the fractional vertices of $Q$ in a given range depends only on the binarization $B_i$ and on $\alpha_1, \dots, \alpha_\ell$, not on $P$ or on the other binarizations. This is what justifies the rank $\operatorname{rk}_B$ of a binarization (Definition 4.7), on which the mission's goal, Theorem 4.23, is built.
--
--   **Formalization Note.** The rank is `propRank` and $\operatorname{lpr}$ is the published `lpr … (yCoords d)`, taken over the $d$ coordinates of $y_i$ in the encoding of $B_i$ as a subset of `Fin (d+1) → ℝ`. The vertices $(\bar x^j, \bar y^j)$ are given as a family `zbar : Fin ℓ → Pt n p d`, and $B_i(\bar x^j_i)$ is the published `slice`.
--
--   Differences from the source:
--   - correction: property P^i printed as "α_j ≤ x̄_i or x̄_i ≥ α_j + 1" → `x̄_i ≤ α_j ∨ α_j + 1 ≤ x̄_i` in `propRank`; reason: the paper itself describes the violating vertices as those with α_j < x̄_i < α_j + 1 (p. 9, paragraph after Observation 4.2; this theorem's hypothesis and proof), while the literal print would make the property equivalent to x̄_i ≥ α_j
--   - encoding: points of Q, B_i(x̄^j_i), lpr with respect to y_{i1},…,y_{id} → `(Fin n → ℝ) × (Fin p → Fin d → ℝ)`, `slice (B i) (xc hpn (zbar j).1 i)`, `lpr … (yCoords d)`; reason: Lean conventions that change no instance
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 10, Theorem 4.6

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

namespace BinaryExtForm.HypercubeRank.Supplement
open BinaryExtForm.HypercubeRank
theorem theorem_4_6 {n p d k ℓ : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ)) (hP : IsPolytope P)
    (hPk : ∀ x ∈ P, ∀ i : Fin p, 0 ≤ xc hpn x i ∧ xc hpn x i ≤ k)
    (B : Fin p → Set (Fin (d + 1) → ℝ)) (hB : ∀ i, IsBinarization d k (B i))
    (hN : ∀ i, IsNatural (B i)) (α : Fin ℓ → ℤ) (i : Fin p)
    (zbar : Fin ℓ → Pt n p d) (hz : ∀ j, zbar j ∈ Set.extremePoints ℝ (BEF hpn P B))
    (hzi : ∀ j, (α j : ℝ) < xc hpn (zbar j).1 i ∧ xc hpn (zbar j).1 i < α j + 1) :
    propRank hpn P B i α =
      lpr (convexHull ℝ (⋃ j, slice (B i) (xc hpn (zbar j).1 i))) (yCoords d) := by sorry
end BinaryExtForm.HypercubeRank.Supplement
