-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_lemma_4
-- name    : ConservativeAD.AutoDiff.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:38.396+00:00
-- url     : https://prove2.me/theorems/aecfb17b-984b-4470-babd-7f907e3d2711
-- title:
--   Lemma 4 — rows of a conservative mapping satisfy the chain rule for the coordinates
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^m$ be locally Lipschitz and $J_F:\mathbb R^n\rightrightarrows\mathbb R^{m\times n}$ a conservative mapping for $F$. Fix a row index $i$ and let $D_i(x)=\{V_{i\cdot} : V\in J_F(x)\}$ be the projection of $J_F$ on its $i$-th row. Then for every absolutely continuous curve $x:[0,1]\to\mathbb R^n$, for almost every $t\in[0,1]$,
--
--   $$
--   \frac{d}{dt}F_i(x(t))=\langle v,\dot x(t)\rangle\qquad\text{for all } v\in D_i(x(t)),
--   $$
--
--   i.e. $D_i$ satisfies the chain-rule property (5) for the $i$-th coordinate $F_i$.
--
--   In the proof of Theorem 8, this lemma passes from the matrix product computed by automatic differentiation (a conservative mapping for the program viewed as a map $\mathbb R^p\to\mathbb R^q$) to its last row, which is the output.
--
--   **Formalization Note** The paper's conclusion is that the projection "is a conservative field for the first coordinate of $F$". Definition 4 imposes no closed graph and no nonempty values on $J_F$, so the projection need not have the closed graph and nonempty compact values Definition 1 requires (for $J_F\equiv\emptyset$ the literal conclusion is false). The statement is therefore read in the chain-rule sense (5), which Lemma 2 identifies with conservativity when the closedness properties hold, and which is what the proof of Theorem 8 uses. It is stated for every row $i$, the first row included.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 13, Lemma 4

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeMap

namespace ConservativeAD.AutoDiff

/-- Lemma 4 (coordinates of conservative mappings), p. 13, in the chain-rule sense: if `F : ℝ^n → ℝ^m`
is locally Lipschitz and `J` is a conservative mapping for `F`, then the projection of `J` on its
`i`-th row satisfies the chain rule (5) for the `i`-th coordinate of `F` (the paper states it for the
first row). -/
theorem lemma_4 {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hF : LocallyLipschitz F)
    (J : EuclideanSpace ℝ (Fin n) → Set (Matrix (Fin m) (Fin n) ℝ))
    (hJ : IsConservativeMap F J) (i : Fin m) :
    HasChainRule (fun x => {v | ∃ V ∈ J x, v = WithLp.toLp 2 (V i)}) (fun x => F x i) := by sorry

end ConservativeAD.AutoDiff
