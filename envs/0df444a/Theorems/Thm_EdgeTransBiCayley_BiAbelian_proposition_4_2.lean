-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiAbelian_proposition_4_2
-- name    : EdgeTransBiCayley.BiAbelian.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:32.286818+00:00
-- url     : https://prove2.me/theorems/51b6412a-12b0-4352-9aff-1dd22738a6ad
-- title:
--   Proposition 4.2 — restrictions on half-arc-transitive bi-abelian graphs
-- statement:
--   Let $\Gamma=\operatorname{BiCay}(H,R,L,S)$ be connected and half-arc-transitive, with $H$ finite and abelian. Then $R\cup L$ is nonempty and contains no element of order two. The equal sizes of $R$ and $L$ are even; $S$ has more than two elements; and every vertex has degree at least six:
--
--   $$
--   R\cup L\ne\varnothing,\quad (\forall x\in R\cup L)\ \operatorname{ord}(x)\ne2,\quad |R|=|L|\in2\mathbb N,\quad |S|>2,\quad \deg_\Gamma(v)\ge6.
--   $$
--
--   These constraints are the second assertion of Proposition 1.3. The lower bound is sharp for the paper’s Example 4.3.
--
--   **Formalization Note** The printed proposition labels its second clause “(a)” again; this statement treats it as clause (b). Valency is the actual graph degree at every vertex.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, pp. 6–7, Proposition 4.2 and its proof

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiAbelian_Setting
open Pointwise

namespace EdgeTransBiCayley.BiAbelian

/-- Proposition 4.2, p. 6: clauses (a), (b), and (c). -/
theorem proposition_4_2 {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected)
    (hhalf : IsHalfArcTransitive D.graph) :
    (D.R ∪ D.L).Nonempty ∧
    (∀ x ∈ D.R ∪ D.L, orderOf x ≠ 2) ∧
    D.R.card = D.L.card ∧ Even D.R.card ∧
    2 < D.S.card ∧
    ∀ v, 6 ≤ D.graph.degree v := by sorry
end EdgeTransBiCayley.BiAbelian
