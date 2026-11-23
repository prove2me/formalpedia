-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_Supplement_observation_4_2
-- name    : BinaryExtForm.HypercubeRank.Supplement.observation_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:01:40.002653+00:00
-- url     : https://prove2.me/theorems/69815c2d-5fec-4ca8-8ec7-69db3d4bb31b
-- title:
--   Observation 4.2, p. 9 — the rank of P^i_{α_1,…,α_ℓ} is a set covering optimum (corrected: P^i read as x̄_i ≤ α_j or x̄_i ≥ α_j + 1)
-- statement:
--   Let $P \subseteq [0,k]^p \times \mathbb R^{n-p}$ be a polytope, $k$ a positive integer, and let $Q$ be the binary extended formulation of $P$ with binarizations $B_1, \dots, B_p \subseteq \mathbb R \times [0,1]^d$ of $x_1, \dots, x_p$ in the range $\{0,\dots,k\}$ (not necessarily natural). Fix $i \in [p]$ and integers $\alpha_1, \dots, \alpha_\ell$. A vertex $(\bar x, \bar y)$ of $Q$ *violates* property $\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}$ if $\alpha_j < \bar x_i < \alpha_j + 1$ for some $j \in [\ell]$. Let $A$ be the $0/1$ matrix with $d$ columns whose rows are the incidence vectors of the fractional supports $\{h \in [d] : \bar y_{ih} \notin \{0,1\}\}$ of the violating vertices. Then the rank of $\mathcal P^i_{\alpha_1,\dots,\alpha_\ell}$ (Definition 4.1) is
--   $$\min\{\mathbf 1 z : Az \ge \mathbf 1,\ z \in \{0,1\}^d\},$$
--   that is, the least size of a set $Z \subseteq [d]$ meeting the fractional support of $\bar y_i$ for every vertex $(\bar x,\bar y)$ of $Q$ that violates the property.
--
--   This set covering form of the rank is one of the two matrices compared in the proof of Theorem 4.6.
--
--   **Formalization Note.** The minimum is the `sInf` of the cardinalities of the sets `Z : Finset (Fin d)` meeting every violating vertex's fractional support; the sets $Z$ are the supports of the vectors $z$. The rank is `propRank` from the supplement's definition file.
--
--   Differences from the source:
--   - correction: property P^i printed as "α_j ≤ x̄_i or x̄_i ≥ α_j + 1" → `x̄_i ≤ α_j ∨ α_j + 1 ≤ x̄_i` (violation `α_j < x̄_i < α_j + 1`); reason: the paper itself describes the violating vertices as those with α_j < x̄_i < α_j + 1 (p. 9, paragraph after Observation 4.2; Theorem 4.6), while the literal print would make the property equivalent to x̄_i ≥ α_j
--   - encoding: set covering optimum over z ∈ {0,1}^d, variables y_{ij_1},…,y_{ij_t} → `sInf` of cardinalities of `Z : Finset (Fin d)`, lists of `Fin d` (repetitions allowed) folded with a local one-step convexification; reason: Lean conventions that change no instance (repeating a variable does not change the convexified set)
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 9, Observation 4.2 (property P^i and Definition 4.1 on the same page)

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

namespace BinaryExtForm.HypercubeRank.Supplement
open BinaryExtForm.HypercubeRank
theorem observation_4_2 {n p d k ℓ : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ)) (hP : IsPolytope P)
    (hPk : ∀ x ∈ P, ∀ i : Fin p, 0 ≤ xc hpn x i ∧ xc hpn x i ≤ k)
    (B : Fin p → Set (Fin (d + 1) → ℝ)) (hB : ∀ i, IsBinarization d k (B i))
    (i : Fin p) (α : Fin ℓ → ℤ) :
    propRank hpn P B i α = sInf {c : ℕ | ∃ Z : Finset (Fin d), Z.card = c ∧
      ∀ z ∈ Set.extremePoints ℝ (BEF hpn P B),
        (∃ j, (α j : ℝ) < xc hpn z.1 i ∧ xc hpn z.1 i < α j + 1) →
          ∃ h ∈ Z, z.2 i h ≠ 0 ∧ z.2 i h ≠ 1} := by sorry
end BinaryExtForm.HypercubeRank.Supplement
