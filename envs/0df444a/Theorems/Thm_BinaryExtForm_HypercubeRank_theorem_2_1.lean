-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_theorem_2_1
-- name    : BinaryExtForm.HypercubeRank.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:20.766784+00:00
-- url     : https://prove2.me/theorems/8ecbbc6f-ea60-47e0-869d-14a00a9383e2
-- title:
--   Theorem 2.1, p. 3 — Balas's sequential convexification theorem
-- statement:
--   Let $Q \subseteq \mathbb R^n$ be a polytope and let $H$ be a set of coordinates such that $0 \le x_i \le 1$ for every $x \in Q$ and every $i \in H$ (the paper's $Q \subseteq [0,1]^h \times \mathbb R^{n-h}$ with $H = [h]$). For a coordinate $i$ write $Q_{x_i} = \operatorname{conv}(\{x \in Q : x_i = 0\} \cup \{x \in Q : x_i = 1\})$. If $i_1, \dots, i_h$ lists every index of $H$ exactly once, then
--   $$\operatorname{conv}\{x \in Q : x_i \in \{0,1\}\ \forall i \in H\} = (((Q_{x_{i_1}})_{x_{i_2}})\dots)_{x_{i_h}}.$$
--
--   Convexifying the 0/1 variables one at a time, each exactly once and in any order, produces the 0/1 hull. In particular $\operatorname{lpr}(Q) \le |H|$, so the lift-and-project rank is a genuine minimum.
--
--   **Formalization Note.** The paper convexifies $x_1, \dots, x_h$ in this order; the statement here allows any set $H$ of 0/1 coordinates and any duplicate-free enumeration `l` of it (`l.Nodup`, `l.toFinset = H`). This matches the paper's remark on p. 3 that the order is irrelevant. `IteratedSplit Q l` applies the convexification steps left to right.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 3, Theorem 2.1

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

open Disjunctive.HigherDim

namespace BinaryExtForm.HypercubeRank
theorem theorem_2_1 {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n)) (hQ : IsPolytope Q)
    (hQH : ∀ p ∈ Q, ∀ i ∈ H, 0 ≤ p i ∧ p i ≤ 1) (l : List (Fin n)) (hl : l.Nodup)
    (hlH : l.toFinset = H) :
    IteratedSplit Q l = intHull Q H := by sorry
end BinaryExtForm.HypercubeRank
