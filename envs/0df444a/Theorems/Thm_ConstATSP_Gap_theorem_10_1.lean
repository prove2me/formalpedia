-- Prove2me | Theorems.Thm_ConstATSP_Gap_theorem_10_1
-- name    : ConstATSP.Gap.theorem_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:48:20.054807+00:00
-- url     : https://prove2.me/theorems/d6477e22-f314-4ef3-aa91-0fec18fe3a02
-- title:
--   Theorem 10.1, p. 49 — Subtour Partition Cover is (4, 2 value(I) + lb(B̄))-light for vertebrate pairs
-- statement:
--   Let $I=(G,\mathcal L,x,y)$ be a laminarly-weighted ATSP instance on at least two vertices and $B$ a subtour such that $(I,B)$ is a **vertebrate pair**: $B$ visits every $S\in\mathcal L$ with $|S|\ge2$. Then Subtour Partition Cover is
--   $$\bigl(4,\ 2\,\mathrm{value}(I)+\mathrm{lb}_I(\bar B)\bigr)\text{-light for } I \text{ and } B:$$
--   for every partition of $V\setminus V(B)$ into nonempty proper sets inducing strongly connected subgraphs there is an Eulerian multiset $F$ with $|\delta^+_F(V_i)|\ge1$ for every part, $w_I(T)\le4\,\mathrm{lb}(T)$ for every subtour $T$ in $F$ disjoint from $V(B)$, and $w_I(F_B)\le2\,\mathrm{value}(I)+\mathrm{lb}_I(\bar B)$ for the union $F_B$ of the subtours of $F$ that meet $B$.
--
--   This is the paper's main technical result on vertebrate pairs; with Theorem 5.1 it yields a tour of weight $2\,\mathrm{value}(I)+O(\mathrm{lb}_I(\bar B))+w_I(B)$.
--
--   **Formalization Note** The paper states this result for a polynomial-time algorithm. Running times are not formalized: following §11 of the paper, which derives the integrality gap "non-constructively", the algorithm is read existentially, i.e. as the existence of the object the algorithm would return. The case $B=\emptyset$ is included; the page treats it through Theorem 4.1 (the instance is then a singleton instance). The instance is required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 49, Theorem 10.1

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem theorem_10_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid)
    (B : E → ℕ) (hB : I.IsVertebrate B) :
    IsLight I B 4 (2 * I.value + I.lbCompl B) := by sorry

end ConstATSP.Gap
