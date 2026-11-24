-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_Supplement_theorem_2_4
-- name    : BicliqueSDP.Chain.Supplement.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:16:59.833788+00:00
-- url     : https://prove2.me/theorems/1129e10c-8e67-46e2-893a-10b0291d7581
-- title:
--   Theorem 2.4 — the half-size clique edge-count reduction
-- statement:
--   Let HALF-SIZE-CLIQUE ask for a clique of half the vertices of an even-order finite simple graph. HALF-SIZE-CLIQUE-EDGE asks the same question with the additional instance condition $4|E|=|V|(|V|-2)$. Then
--
--   $$\mathrm{HALF\text{-}SIZE\text{-}CLIQUE}\ \le_P\ \mathrm{HALF\text{-}SIZE\text{-}CLIQUE\text{-}EDGE}.$$
--
--   The reduction is a many-one reduction computed by a Turing machine in polynomially many steps, with equivalence on every input string. This supplies the first reduction in the paper's complexity chain.
--
--   Differences from the source:
--   - encoding: The source leaves the graph encoding implicit → The statement uses dense bit-string graph codes and the published CookPvsNP.PolyReducible; reason: This fixes an ordinary polynomially reasonable encoding and requires actual polynomial-time computation, including rejection of malformed or invalid instances.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 8, Theorem 2.4

import Definitions.Def_BicliqueSDP_Chain_Supplement_Problems
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement

/-- Theorem 2.4: an actual polynomial-time many-one reduction on all bit strings. -/
theorem theorem_2_4 : CookPvsNP.PolyReducible halfSizeClique halfSizeCliqueEdge := by sorry

end BicliqueSDP.Chain.Supplement
