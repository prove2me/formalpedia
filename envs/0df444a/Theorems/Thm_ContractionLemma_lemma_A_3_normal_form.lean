-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_3_normal_form
-- name    : ContractionLemma.lemma_A_3_normal_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:29.936093+00:00
-- url     : https://prove2.me/theorems/69de3ef7-7dab-46fc-a14b-c1cf64d9ddfb
-- title:
--   Lemma A.3 — normal form: $Z(G)=c\cdot Z(G^\prime)$, $G^\prime$ bipartite
-- statement:
--   Let $G$ be a network over a commutative ring, with normal form $G'$ and scalar $c$, the product of the entries of the isolated vertices. Then
--
--   $$
--   Z(G)=c\cdot Z(G').
--   $$
--
--   The network $G'$ is bipartite with no isolated vertices, $|E(G')|=2|E(G)|$, $G'$ has at most $3|E(G)|$ vertices, its maximum degree is at most $\max(2,\text{maximum degree of }G)$, and every new vertex has the equality table $[x=y]$. Moreover, for every entry machine there are a machine and a constant $C$ such that the machine computes the description of $G'$ and the scalar $c$ from the encoded instance in at most $C(N+1)^C(1+\tau)$ steps, where $\tau$ bounds the entry machine's time.
--
--   This is the first reduction of the contraction lemma: all later steps work with bipartite networks.
--
--   **Formalization Note** Bipartiteness holds by construction of the type. The lemma states no space bound, so the machine clause has none.
--
--   Differences from the source:
--   - reading: in polynomial time plus polynomially many evaluations of table values → some machine within C(N+1)^C(1+τ) steps, for every entry machine and τ; reason: each evaluation costs at most τ steps, and the rest is polynomial in the encoded instance
--   - encoding: G′ is a graph with vertices and edges listed → row vertices the non-isolated old vertices, column vertices E, edges E × Bool; reason: a concrete presentation of the same graph
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.3, p.52; proof p.82

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Net
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Instance
import Definitions.Def_ContractionLemma_Net_normalForm

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT.Computation

/-- **Lemma A.3 (Normal form)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.52 (PDF p.55); proof p.82.

1. For every network `G` over a commutative ring, the normal form `G′ = normalForm G` (every
   edge subdivided by an equality vertex, isolated vertices deleted) and the scalar
   `c = nfScalar G` satisfy `Z(G) = c · Z(G′)`; `G′` is bipartite (by construction) with no
   isolated vertex, `|E(G′)| = 2|E(G)|`, at most `3|E(G)|` vertices, maximum degree at most
   `max(2, maximum degree of G)`, and every new vertex has the equality table `[x = y]`.
2. (computation) For every entry machine `E` there are a machine `A` and a constant `C` such
   that, for every instance whose tables (in `R_{P,ℓ}`) `E` computes within time `τ`, `A`
   outputs the description of `G′` and the scalar `c` in at most `C (N+1)^C (1 + τ)` steps:
   polynomial time plus polynomially many evaluations of table values.

**Formalization Note.** The construction is explicit (`Net.normalForm`); the description of
`G′` is `Instance.nfWord`. The lemma states no space bound, so none is claimed (the space
bound in `RunsWithin` is existentially quantified per instance). -/
theorem lemma_A_3_normal_form :
    (∀ {V E R : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [CommRing R]
        (G : Net V E R),
      G.Z = G.nfScalar * G.normalForm.Z ∧
      (∀ u, 0 < G.normalForm.rowDeg u) ∧ (∀ e, 0 < G.normalForm.colDeg e) ∧
      Fintype.card (E × Bool) = 2 * Fintype.card E ∧
      Fintype.card ({v : V // ¬ G.IsIsolated v} ⊕ E) ≤ 3 * Fintype.card E ∧
      (∀ u, G.normalForm.rowDeg u ≤ max 2 G.maxDeg) ∧
      (∀ e, G.normalForm.colDeg e ≤ max 2 G.maxDeg) ∧
      (∀ e z, G.normalForm.colTable e z =
        if z ⟨(e, false), rfl⟩ = z ⟨(e, true), rfl⟩ then 1 else 0)) ∧
    (∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
      ∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (C : ℕ),
      ∀ (I : Instance) (T : I.Tables (TruncPoly I.P)) (τ σ : ℝ), 0 ≤ τ →
        I.EntryComputes E outE T τ σ →
        ∃ σA : ℝ, RunsWithin A outA I.encode (I.nfWord (I.net T).nfScalar)
          (C * ((I.encode.length : ℝ) + 1) ^ C * (1 + τ)) σA) := by sorry

end ContractionLemma
