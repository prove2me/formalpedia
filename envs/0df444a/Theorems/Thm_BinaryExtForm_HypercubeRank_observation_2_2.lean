-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_observation_2_2
-- name    : BinaryExtForm.HypercubeRank.observation_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:26.355097+00:00
-- url     : https://prove2.me/theorems/1c446d53-d202-41d8-8008-04f60ee1acb2
-- title:
--   Observation 2.2, p. 4 — the lift-and-project rank is the optimum of a set covering problem
-- statement:
--   Let $Q \subseteq \mathbb R^n$ be a polytope whose coordinates in $H$ lie in $[0,1]$. Let $V_F$ be the set of vertices of $Q$ having at least one fractional coordinate (a value outside $\{0,1\}$) among the coordinates in $H$, and let $A_Q$ be the $0/1$ matrix whose rows are the incidence vectors of the fractional supports $\{i \in H : 0 < v_i < 1\}$ of the vertices $v \in V_F$. Then
--   $$\operatorname{lpr}(Q) = \min\{\mathbf 1 z : A_Q z \ge \mathbf 1,\ z \in \{0,1\}^H\}.$$
--   Equivalently, $\operatorname{lpr}(Q)$ is the minimum size of a set $Z \subseteq H$ that contains, for every vertex of $Q$ with a fractional coordinate in $H$, at least one of its fractional coordinates.
--
--   This turns the convexification count into a purely combinatorial hitting-set problem on the vertex set of $Q$; the rank of a binarization is analysed through it.
--
--   **Formalization Note.** $z \in \{0,1\}^H$ is a subset $Z \subseteq H$ and $\mathbf 1 z = |Z|$; duplicate rows of $A_Q$ do not change the problem, so it is stated vertex by vertex. $Z = H$ is always feasible, so the `sInf` on the right is a true minimum. As in `lpr`, $H$ is any set of coordinates instead of the first $h$.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, pp. 3–4, Observation 2.2 (with the definitions of V_F, F and A_Q on pp. 3–4)

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem observation_2_2 {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n)) (hQ : IsPolytope Q)
    (hQH : ∀ p ∈ Q, ∀ i ∈ H, 0 ≤ p i ∧ p i ≤ 1) :
    lpr Q H = sInf {c : ℕ | ∃ Z : Finset (Fin n), Z ⊆ H ∧ Z.card = c ∧
      ∀ v ∈ Set.extremePoints ℝ Q, (∃ i ∈ H, v i ≠ 0 ∧ v i ≠ 1) →
        ∃ i ∈ Z, v i ≠ 0 ∧ v i ≠ 1} := by sorry
end BinaryExtForm.HypercubeRank
