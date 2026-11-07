-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_12_2_one_monomial_splits
-- name    : ContractionLemma.lemma_A_12_2_one_monomial_splits
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:12.182954+00:00
-- url     : https://prove2.me/theorems/093ae965-2216-4265-952a-ca3ccd8768f9
-- title:
--   Lemma A.12.2 — one monomial splits: the $\beta$-term is $\prod_g Z(G_{g,\beta})$
-- statement:
--   In the setting of Lemma A.12.1, fix an exponent vector $\beta$. The $\beta$-term equals
--
--   $$
--   \prod_g Z(G_{g,\beta}),
--   $$
--
--   a product over the level-$i$ groups $g$, where each $G_{g,\beta}$ is a bipartite network with at most $3M/32<M/8$ edges that keeps the old tables of group $g$ unchanged and adds one packet tensor per packet, of degree at most $2L$. Each entry of a packet tensor can be computed in time $\exp(O(L\log(s+p')))$ and space $\mathrm{poly}(s+p')$, without querying the old tables.
--
--   This is the step that makes the recursion possible: after a monomial is fixed, nothing passes between the groups, and a packet tensor's cost does not compound with the depth.
--
--   **Formalization Note** Bipartiteness, the unchanged old tables and one packet tensor per packet hold by construction of $G_{g,\beta}$. In the cost clause one machine works for all networks. Its input is the packet data, which holds no table, and its output is the entry modulo $2^{p'}$.
--
--   Differences from the source:
--   - reading: each entry can be computed in time exp(O(L log(s + p′))) and space poly(s + p′) → one machine within C·2^{C·L·log₂(s+p′+2)} steps and C(s+p′+2)^C cells, on the packet data word; reason: the paper names no input encoding; the word holds exactly what the proof reads and no table
--   - reading: the setting of the recursion, stated around the lemma → L ≤ s, f of degree 4⌈log₂ s⌉ with coefficients in {0, 1} (p.96), β of total weight below p′; reason: the recursion has L ≤ s^{1/1000}, tests the 0/1 candidates for f, and uses only surviving β; the bound does not depend on β, whose entries are in the input
--   - encoding: log(s + p′), and the entry of the exact tensor → log₂(s+p′+2), and its canonical lift modulo 2^{p′} (p.96); reason: the logarithm is positive for all inputs, and the algorithm stores the canonical lift
--   - reading: in the setting of Lemma A.12.1 (part 1) → orientation, small groups and M ≥ LQ as hypotheses; reason: these are the facts of Lemma A.9 the identity and the edge bound use; M ≥ LQ gives M ≥ 1 for 3M/32 < M/8
--   - reading: a node z_j ∈ O → a binary node ∑ b_k U^k; reason: these are the nodes defined on p.96
--   - generalization: O = Z_(2)[U]/(f) with f of degree 4λ (part 1) → every monic f with f mod 2 irreducible, of any degree; reason: the paper picks one such f by search; degree 4λ is a special case
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.12.2, p.68; proof pp.90–91

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_Placement
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_zoom
import Definitions.Def_ContractionLemma_Et
import Definitions.Def_ContractionLemma_aSlot
import Definitions.Def_ContractionLemma_NodeField
import Definitions.Def_ContractionLemma_Splitting_modeSet
import Definitions.Def_ContractionLemma_Splitting_childNet
import Definitions.Def_ContractionLemma_Splitting_betaTerm
import Definitions.Def_ContractionLemma_Splitting_packetInput

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT.Computation
open Polynomial

/-- **Lemma A.12.2 (One monomial splits)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.68 (PDF p.71); proof pp.90–91.

In the setting of Lemma A.12.1 (a bipartite network with `M` edges, labels and packets as in
Lemma A.9, `t ∈ E \ {−L}` of level `i`, a precision `p′`, a node `z_j`), fix an exponent vector
`β`.
1. The `β`-term equals `∏_g Z(G_{g,β})`, the product over the level-`i` groups `g`; each `G_{g,β}`
   is a bipartite network with at most `3M/32 < M/8` edges that keeps the old tables of `g`
   unchanged and adds one packet tensor per packet, of degree at most `2L`.
2. (cost) Each entry of a packet tensor can be computed in time `exp(O(L log(s + p′)))` and space
   `poly(s + p′)`, without querying the old tables.

**Formalization Note.** The modes, the `β`-term and `G_{g,β}` are the constructions of the proof
(`Splitting.modeSet`, `Splitting.betaTerm`, `Splitting.childNet`); bipartiteness, the unchanged
old tables and "one packet tensor per packet" hold by construction. In part 2 one machine works
for all networks: its input `Splitting.packetInput` holds the packet data and no table, its output
is the entry modulo `2^{p′}` (`Splitting.oWord`, the canonical lift of p.96). The setting of the
recursion is recorded as `L ≤ s`, `f` monic of degree `4⌈log₂ s⌉` with coefficients in `{0, 1}`
and `f mod 2` irreducible (p.96), and `β` of total weight below `p′`, the only `β` the algorithm
uses (the bound does not depend on `β`, whose entries are in the input). -/
theorem lemma_A_12_2_one_monomial_splits :
    (∀ {U W E : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] [Fintype E]
        [DecidableEq E] (f : ℤ[X]) (dg : ℕ) (_ : IsNodePoly f dg) (a : ℕ)
        (G : BipNet U W E (NodeField f)) (pk : Packing U W E a),
        pk.Orientation G.rowOf G.colOf → pk.SmallGroups G.rowOf G.colOf →
        2 ^ a * 64 ^ (2 * a) ≤ Fintype.card E →
        ∀ t ∈ easyPts a, t ≠ -(2 ^ a : ℤ) → ∀ i : ℕ, i = padicValInt 2 t →
        ∀ (p' : ℕ) (b : Fin f.natDegree → Bool) (β : Splitting.Mode G pk i p' → ℕ),
        Splitting.betaTerm G pk t i (binNode f b) p' β =
            ∏ g : Fin 64, (Splitting.childNet G pk t i (binNode f b) p' g β).Z ∧
          ∀ g : Fin 64,
            (Fintype.card (Splitting.Bits G pk i g) : ℝ) ≤ 3 * Fintype.card E / 32 ∧
            (3 * Fintype.card E / 32 : ℝ) < Fintype.card E / 8 ∧
            ∀ P, (Splitting.childNet G pk t i (binNode f b) p' g β).colDeg P ≤ 2 * 2 ^ a) ∧
    (∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (C : ℕ),
      ∀ {U W E : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] [Fintype E]
        [DecidableEq E] (s : ℕ) (f : ℤ[X]), IsNodePoly f (4 * lam s) →
        (∀ k, f.coeff k = 0 ∨ f.coeff k = 1) →
        ∀ (a : ℕ), 2 ^ a ≤ s →
        ∀ (G : BipNet U W E (NodeField f)) (pk : Packing U W E a),
        pk.Orientation G.rowOf G.colOf →
        ∀ t ∈ easyPts a, t ≠ -(2 ^ a : ℤ) → ∀ i : ℕ, i = padicValInt 2 t →
        ∀ (p' : ℕ) (b : Fin f.natDegree → Bool) (g : Fin 64) (β : Splitting.Mode G pk i p' → ℕ),
        β ∈ Splitting.survivors G pk i p' →
        ∀ (P : Fin pk.np) (zz : {x : Splitting.Bits G pk i g // Splitting.bitPacket x = P} → Bool),
        RunsWithin A outA
          (Splitting.packetInput s f G pk t i b p' g β P
            (Splitting.bitY G pk i g P zz) (Splitting.bitX G pk i g P zz))
          (Splitting.oWord f p' (Splitting.packetTensor G pk t i (binNode f b) p' g β P zz))
          ((C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * 2 ^ a * Real.logb 2 ((s : ℝ) + p' + 2)))
          ((C : ℝ) * ((s : ℝ) + p' + 2) ^ C)) := by sorry

end ContractionLemma
