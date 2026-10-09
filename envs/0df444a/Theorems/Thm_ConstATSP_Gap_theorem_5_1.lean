-- Prove2me | Theorems.Thm_ConstATSP_Gap_theorem_5_1
-- name    : ConstATSP.Gap.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:48:16.142691+00:00
-- url     : https://prove2.me/theorems/a8cb3e11-b8f6-49b3-ab68-155a53675175
-- title:
--   Theorem 5.1, p. 17 — a light algorithm for Subtour Partition Cover yields a tour of weight ≤ 5α lb(B̄) + β + w(B)
-- statement:
--   Let $I=(G,\mathcal L,x,y)$ be a laminarly-weighted ATSP instance on at least two vertices, $B$ a subtour, and $\alpha\ge0$, $\beta$ real numbers such that Subtour Partition Cover is $(\alpha,\beta)$-light for $I$ and $B$: for every partition of $V\setminus V(B)$ into nonempty proper sets inducing strongly connected subgraphs there is a collection $F$ of subtours covering every part ($|\delta^+_F(V_i)|\ge1$), with $w_I(T)\le\alpha\,\mathrm{lb}(T)$ for each subtour $T$ in $F$ disjoint from $V(B)$ and $w_I(F_B)\le\beta$ for the subtours meeting $B$. Then $G$ has a tour $F$ with
--   $$w_I(F)\le 5\alpha\,\mathrm{lb}_I(\bar B)+\beta+w_I(B),$$
--   where $\mathrm{lb}_I(\bar B)=\mathrm{lb}_I(V\setminus V(B))$.
--
--   This is the reduction from ATSP to Subtour Partition Cover on which every later bound of the paper rests; the page adds an algorithmic version with factor $9(1+\varepsilon)$ in place of $5$, which is not part of this statement.
--
--   **Formalization Note** Only the first (existential) sentence of Theorem 5.1 is formalized; the second sentence, the polynomial-time variant with constant $9(1+\varepsilon)$, is not. The hypothesis $\alpha\ge0$ is not written on the page; it is the role of $\alpha$ as a lightness factor, and without it the statement is false: on $V=\{a,b\}$ with a loop at $a$ and edges $a\to b$, $b\to a$, $x\equiv1$, $\mathcal L=\{\{b\}\}$, $y_b=1$ and $B$ the loop, the pair is $(-1,2)$-light while every tour weighs at least $2>5\cdot(-1)\cdot2+2+0$. The instance is required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 17, Theorem 5.1 (first sentence)

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem theorem_5_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid)
    (B : E → ℕ) (hB : IsSubtour I.G B) (α β : ℝ) (hα : 0 ≤ α) (hL : IsLight I B α β) :
    ∃ F : E → ℕ, IsTour I.G F ∧ I.wt F ≤ 5 * α * I.lbCompl B + β + I.wt B := by sorry

end ConstATSP.Gap
