-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiAbelian_proposition_4_1_a
-- name    : EdgeTransBiCayley.BiAbelian.proposition_4_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:16.277625+00:00
-- url     : https://prove2.me/theorems/b11f27d8-ea76-4baf-8acd-03b5d930a721
-- title:
--   Proposition 4.1(a) — regular action for the bipartite case
-- statement:
--   Let $H$ be a finite abelian group and let $\Gamma=\operatorname{BiCay}(H,R,L,S)$ be connected. If $R=L=\varnothing$, inversion $\alpha(h)=h^{-1}$ defines the automorphism $\delta_{\alpha,1,1}$ that exchanges the two copies of $H$. Together with $R(H)$ it generates a group acting regularly on all vertices:
--
--   $$
--   \forall u,v\in V(\Gamma),\quad \exists!\,\varphi\in\langle R(H),\delta_{\alpha,1,1}\rangle:\ \varphi(u)=v.
--   $$
--
--   This supplies the vertex-transitive conclusion when no edge lies inside either copy of $H$.
--
--   **Formalization Note** The statement also records that $\delta_{\alpha,1,1}$ has order two and normalises $R(H)$, specifying the semidirect product in the paper.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 6, Proposition 4.1(a)

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiAbelian_Setting
open Pointwise

namespace EdgeTransBiCayley.BiAbelian

/-- Proposition 4.1(a), p. 6: inversion swaps the two fibres and generates,
with R(H), a regular vertex action. -/
theorem proposition_4_1_a {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected)
    (hR : D.R = ∅) (hL : D.L = ∅) :
    ∃ δ : D.graph ≃g D.graph,
      (∀ v, δ v = deltaPerm (MulEquiv.inv H) 1 1 v) ∧
      δ * δ = 1 ∧ δ ∈ normRH D ∧
      ∀ u v : H ⊕ H,
        ∃! φ : D.graph ≃g D.graph,
          φ ∈ Subgroup.closure (Set.insert δ (Set.range (rightMul D))) ∧ φ u = v := by sorry
end EdgeTransBiCayley.BiAbelian
