-- Prove2me | Theorems.Thm_ConstATSP_Gap_theorem_4_1
-- name    : ConstATSP.Gap.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:48:05.918971+00:00
-- url     : https://prove2.me/theorems/a3164734-dc7c-45a5-9a7f-be0c1ce524da
-- title:
--   Theorem 4.1, p. 14 — Subtour Partition Cover is (2, 0)-light on singleton instances with B = ∅
-- statement:
--   Let $I=(G,\mathcal L,x,y)$ be a laminarly-weighted ATSP instance on at least two vertices that is a **singleton instance**, i.e. every set of $\mathcal L$ is a singleton, and take the empty subtour $B=\emptyset$. Then for every partition $(V_1,\dots,V_k)$ of $V$ into nonempty proper sets $V_i\subsetneq V$, each inducing a strongly connected subgraph, there is an Eulerian edge multiset $F$ with
--   $$|\delta^+_F(V_i)|\ge 1\quad(i=1,\dots,k)\qquad\text{and}\qquad w_I(T)\le 2\,\mathrm{lb}(T)\ \text{ for every subtour } T \text{ in } F .$$
--   In the paper's terms, Subtour Partition Cover admits a $(2,0)$-light algorithm for singleton instances with $B=\emptyset$ (the $\beta$-condition is vacuous, since no subtour meets $B=\emptyset$).
--
--   Combined with Theorem 5.1 this gives the constant-factor bound for singleton instances, the base case of the paper's reduction chain.
--
--   **Formalization Note** The paper states this result for a polynomial-time algorithm. Running times are not formalized: following §11 of the paper, which derives the integrality gap "non-constructively", the algorithm is read existentially, i.e. as the existence of the object the algorithm would return. The partition parts are required to be proper subsets of $V$: the one-part partition $(V)$ admits no solution because $\delta^+(V)=\emptyset$, and the paper's proof uses $x(\delta^-(V_i))\ge1$, which needs $V_i\ne V$. The instance is required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 14, Theorem 4.1

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem theorem_4_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid)
    (hS : I.IsSingleton) :
    IsLight I 0 2 0 := by sorry

end ConstATSP.Gap
