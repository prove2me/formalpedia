-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiDihedrant_proposition_2_1_b
-- name    : EdgeTransBiCayley.BiDihedrant.proposition_2_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:39:39.605863+00:00
-- url     : https://prove2.me/theorems/0af3ed64-7575-4790-81ae-625ac132e3a1
-- title:
--   Proposition 2.1(b) — S may be taken to contain 1, up to graph isomorphism
-- statement:
--   Let $\Gamma = \mathrm{BiCay}(H, R, L, S)$ be a connected bi-Cayley graph over a finite group $H$. Then there are subsets $R', L', S' \subseteq H$ forming valid bi-Cayley data, with
--
--   $$
--   1 \in S', \qquad R' = R, \qquad |S'| = |S|, \qquad \mathrm{BiCay}(H, R, L, S) \cong \mathrm{BiCay}(H, R', L', S').
--   $$
--
--   This is the normalisation used at the start of the proof of Theorem 6.1: one may assume $1 \in S$ without changing the graph.
--
--   **Formalization Note** The paper's statement only says that $S$ "can be chosen to contain the identity (up to graph isomorphism)". The Lean statement also records $R' = R$ and $|S'| = |S|$, which hold for the standard choice; they are part of what "choosing $S$" means here, since the rest of the data is unchanged up to conjugating $L$. The isomorphism is a `SimpleGraph` isomorphism `D.graph ≃g D'.graph`. Connectedness is the hypothesis of Proposition 2.1.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 4, Proposition 2.1(b)

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Setting
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

theorem proposition_2_1_b {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected) :
    ∃ D' : BiCayData H, (1 : H) ∈ D'.S ∧ D'.R = D.R ∧ D'.S.card = D.S.card ∧
      Nonempty (D.graph ≃g D'.graph) := by sorry

end EdgeTransBiCayley.BiDihedrant
