-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_lemma_3_1
-- name    : ConicQuadIPM.Complementarity.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:35.36702+00:00
-- url     : https://prove2.me/theorems/1d992bfd-8874-4709-96c2-b3253332d3ae
-- title:
--   Lemma 3.1, p. 9 — x, s ∈ K are complementary iff XⁱSⁱeⁱ = SⁱXⁱeⁱ = 0 for every cone i
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be a product of cones, each of which is $\mathbb R_+$, a quadratic cone $K^q$ or a rotated quadratic cone $K^r$ (Definition 3.1), and let $T^i$ be the matrices of Definition 3.2. For $x,s\in K$ put
--   $$
--   X^i=\operatorname{mat}(T^ix^i),\qquad S^i=\operatorname{mat}(T^is^i),\qquad
--   \operatorname{mat}(v)=\begin{pmatrix}v_1&v_{2:n}^T\\v_{2:n}&v_1I\end{pmatrix},
--   $$
--   and let $e^i\in\mathbb R^{n^i}$ be the first unit vector. Then $x$ and $s$ are complementary, $x^Ts=0$, if and only if
--   $$
--   X^iS^ie^i=S^iX^ie^i=0,\qquad i=1,\dots,k. \tag{20}
--   $$
--
--   Lemma 3.1 turns the single scalar condition $x^Ts=0$ into the block-wise system (20), which is the form of complementarity that the central path (21) relaxes and that Newton's method linearises.
--
--   **Formalization Note.** Vectors are `Fin d → ℝ` with the paper's $x_1$ at index `0`; points of $K$ are stored block by block and $x^Ts=\sum_i (x^i)^Ts^i$. Norms inside the cone definitions are Euclidean, written out. The block dimensions ($n^i=1$ for $\mathbb R_+$, $n^i\ge1$ for $K^q$, $n^i\ge2$ for $K^r$) are implicit in the paper and added as the hypothesis `WellFormed`. The hypothesis "$x,s\in K$" is taken literally ($K$ is self-dual, so this is primal and dual feasibility).
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 9, Lemma 3.1 and (20); proof in the Appendix, pp. 36–37

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem lemma_3_1 {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ)
    (hx : inK kind x) (hs : inK kind s) :
    ∑ i, x i ⬝ᵥ s i = 0 ↔
      ∀ i : Fin k,
        (arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1 = 0 ∧
        (arrow (Tmat (kind i) (n i) *ᵥ s i) * arrow (Tmat (kind i) (n i) *ᵥ x i)) *ᵥ e1 = 0 := by sorry

end ConicQuadIPM.Complementarity
