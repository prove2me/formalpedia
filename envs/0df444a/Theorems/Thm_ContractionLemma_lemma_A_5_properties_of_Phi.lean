-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_5_properties_of_Phi
-- name    : ContractionLemma.lemma_A_5_properties_of_Phi
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:51.422408+00:00
-- url     : https://prove2.me/theorems/001c1d8a-6a2f-4364-9cb8-fb300d70a314
-- title:
--   Lemma A.5 — properties of $\Phi$: degree, $\Phi(I)=Z(G)$, block wirings split
-- statement:
--   Let $G$ be a bipartite network with $M$ edges and $\Phi$ as in (5).
--
--   1. $\Phi$ is a polynomial of degree at most $M$ in the entries of $W$, and $\Phi(I)=Z(G)$.
--   2. If $W$ is block diagonal for a partition of the vertices into groups $g$, then
--   $$
--   \Phi(W)=\prod_g\Phi_g(W_g),
--   $$
--   the product over all groups $g$.
--
--   This is the reason a wiring helps: block diagonal wirings turn one contraction into independent smaller ones.
--
--   **Formalization Note** Groups are the fibres of two maps from the row and column vertices to a finite type; an empty group contributes the factor $1$.
--
--   Differences from the source:
--   - generalization: wiring W over the ring of the network → in (b), W with entries in any commutative R-algebra S; reason: the tables are mapped into S; S = R gives the source
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.5, p.54; proof pp.82–83

import Mathlib
import Definitions.Def_ContractionLemma_Net
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi

set_option autoImplicit false

namespace ContractionLemma

/-- **Lemma A.5 (Properties of `Φ`)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.54 (PDF p.57); proof pp.82–83.

Let `G` be a bipartite network with `M` edges and `Φ` as in (5).
(a) `Φ` is a polynomial of degree at most `M` in the entries of `W`, and `Φ(I) = Z(G)`.
(b) If `W` is block diagonal for a partition of the vertices into groups, then
`Φ(W) = ∏_g Φ_g(W_g)`, the product over all groups.

**Formalization Note.** Groups are the fibres of `rowGrp`, `colGrp` over a finite type `Γ`
of group names (an empty group contributes the factor `1`). Part (b) is stated for wirings with
entries in any commutative `R`-algebra `S`. -/
theorem lemma_A_5_properties_of_Phi {U W E R : Type*} [Fintype U] [Fintype W] [Fintype E]
    [DecidableEq E] [CommRing R] (G : BipNet U W E R) :
    (G.Phi.totalDegree ≤ Fintype.card E ∧ G.PhiAt (1 : Matrix E E R) = G.Z) ∧
    (∀ {Γ S : Type*} [Fintype Γ] [DecidableEq Γ] [CommRing S] [Algebra R S]
        (rowGrp : U → Γ) (colGrp : W → Γ) (Wm : Matrix E E S),
        G.IsBlockDiag rowGrp colGrp Wm →
        G.PhiAt Wm = ∏ g, G.PhiGroup rowGrp colGrp g Wm) := by sorry

end ContractionLemma
