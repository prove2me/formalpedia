-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_eq_3
-- name    : EvenCycleTuran.EvenCount.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:48.001006+00:00
-- url     : https://prove2.me/theorems/fb6a3040-bc85-47c3-bad8-9dcb1f4c161e
-- title:
--   (3), p. 10 — 4l·𝒩(C_{2l}, G) ≤ Σ over l-tuples of Π f(v_j, v_{j+1}), and the AM–GM step
-- statement:
--   Let $l\ge3$ and let $G$ be a finite simple graph. Sum over all $l$-tuples $(v_1,\dots,v_l)$ of distinct vertices, with $v_{l+1}=v_1$. Then
--   $$\mathcal N(C_{2l},G)\le\frac1{4l}\sum_{(v_1,\dots,v_l)}\prod_{j=1}^{l}f(v_j,v_{j+1})\le\frac1{4l}\sum_{(v_1,\dots,v_l)}\frac{f^2(v_1,v_2)+f^2(v_2,v_3)}{2}\prod_{j=3}^{l}f(v_j,v_{j+1}).$$
--
--   The first inequality holds because the $C_{2l}$'s whose even vertices are $v_1,\dots,v_l$ in this order number at most $\prod_j f(v_j,v_{j+1})$, and each $C_{2l}$ arises from exactly $4l$ tuples. The second is $xy\le(x^2+y^2)/2$. The resulting sum is bounded with Claim 1 in the proof of Theorem 10.
--
--   **Formalization Note** Tuples of distinct vertices are injective maps $\{0,\dots,l-1\}\hookrightarrow V$; the index $j+1$ is taken mod $l$ (`finRotate`), and the paper's $v_1,v_2,v_3$ are the indices $0,1,2$. The first inequality is stated multiplied by $4l$. The hypothesis $l\ge3$ is the range of Theorem 10's upper bound; at $l=2$ the factor $4l$ would be wrong.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 10, eq. (3) and the paragraph before it

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem eq_3 (l : ℕ) (hl : 3 ≤ l) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 * l * G.copyCount (cycleGraph (2 * l)) : ℕ) : ℝ) ≤
        ∑ v : Fin l ↪ V, ∏ j : Fin l, (EvenCycleTuran.C4Count.codeg G (v j) (v (finRotate l j)) : ℝ) ∧
      ∑ v : Fin l ↪ V, ∏ j : Fin l, (EvenCycleTuran.C4Count.codeg G (v j) (v (finRotate l j)) : ℝ) ≤
        ∑ v : Fin l ↪ V,
          ((EvenCycleTuran.C4Count.codeg G (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) : ℝ) ^ 2 +
              (EvenCycleTuran.C4Count.codeg G (v ⟨1, by omega⟩) (v ⟨2, by omega⟩) : ℝ) ^ 2) / 2 *
            ∏ j ∈ univ.filter (fun j : Fin l => 2 ≤ (j : ℕ)),
              (EvenCycleTuran.C4Count.codeg G (v j) (v (finRotate l j)) : ℝ) := by sorry

end EvenCycleTuran.EvenCount
