-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_Supplement_lemma_2_6
-- name    : BicliqueSDP.Chain.Supplement.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:17:40.340798+00:00
-- url     : https://prove2.me/theorems/748138e3-1c42-43cc-b278-dc68372b1868
-- title:
--   Lemma 2.6 (corrected: allow extra left edge gadgets) — maximal independent sets of H_G
-- statement:
--   Let $G=(V,E)$ be any finite simple graph, with $n=|V|$, $m=|E|$, and let $H_G$ be exactly the graph in Definition 2.5. The corrected characterization is as follows. For each maximal independent set $I$, there are $A\subseteq V$ and $F\subseteq E$ containing every edge incident to $A$ such that
--
--   $$I\cap V_1=\{v_1:v\in A\}\cup\bigcup_{e\in F}L_e,\qquad
--   I\cap V_2=\{v_2:v\notin A\}\cup\bigcup_{e\notin F}R_e.$$
--
--   Every maximal independent set is maximum, and
--
--   $$\alpha(H_G)=n+m(n+1).$$
--
--   Conversely, for every $A$ and every such $F$, the displayed sets form a maximum independent set. In particular, this retains the source's converse for the canonical choice of $F$ equal to the edges incident to $A$. This supports Theorem 2.8.
--
--   **Formalization Note** The printed characterization is false for $G=K_2$: the set $R_V\cup L_e$ is maximal and maximum but has $A=\varnothing$ and $F=\{e\}$. The repair changes the characterization without restricting graphs or independent sets; its evidence is retained in DISPROOF.md.
--
--   Differences from the source:
--   - correction: Lemma 2.6 requires F to equal the edges incident to A for every maximal independent set → F may be any superset of the edges incident to A; the maximum-cardinality and converse clauses are retained; reason: For G=K2, RV union Le is maximal but violates the printed form; Definition 2.5 permits choosing Le even when neither endpoint is in A, and maximality forces exactly one complete gadget side per edge.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 9, Lemma 2.6

import Definitions.Def_BicliqueSDP_Chain_Supplement_Gadget
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement

/-- Lemma 2.6, corrected: the chosen left edge set F may contain additional edges
not incident to A. No graph or independent set is excluded. The other clauses are unchanged. -/
theorem lemma_2_6 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    alpha (HGEdge G) = (Fintype.card V : ℝ) +
      (Nat.card G.edgeSet : ℝ) * (Fintype.card V + 1) ∧
    (∀ L R : Finset (HGSide G), IsMaximalPair (HGEdge G) L R →
      (∃ (A : Finset V) (F : Finset (Edge G)),
        incidentEdges G A ⊆ F ∧ L = formLeft G A F ∧ R = formRight G A F) ∧
      IsMaximumPair (HGEdge G) L R) ∧
    (∀ (A : Finset V) (F : Finset (Edge G)), incidentEdges G A ⊆ F →
      IsMaximumPair (HGEdge G) (formLeft G A F) (formRight G A F)) := by sorry

end BicliqueSDP.Chain.Supplement
