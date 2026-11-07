-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_12_splitting_near_easy_point
-- name    : ContractionLemma.lemma_A_12_splitting_near_easy_point
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:45.329409+00:00
-- url     : https://prove2.me/theorems/dfd7f8ca-89d0-4268-ae3c-6b4a2510ae9a
-- title:
--   Lemma A.12 — splitting near an easy point
-- statement:
--   Let $G$ be a bipartite network with $M$ edges and tables in the node ring $\mathcal O$, with labels and packets as in Lemma A.9, and rewiring polynomial $F$. Fix $t\in\mathcal E\setminus\{-L\}$ of level $i$, a precision $p'$ and a node $z_j\in\mathcal O$. Then the modes $\xi$, with weights $w_\xi\ge 1$, satisfy:
--
--   1. there are at most $6M/D_i$ modes of each weight, where $D_i=L/2^i$;
--   2. with the networks $G_{g,\beta}$, one for each level-$i$ group $g$,
--   $$
--   F(t+\alpha z_j)\equiv\sum_{\beta:\ \sum_\xi w_\xi\beta_\xi<p'}\ \prod_g Z(G_{g,\beta})\pmod{2^{p'}};
--   $$
--   3. each $G_{g,\beta}$ is bipartite with fewer than $M/8$ edges; it keeps the old tables of group $g$ unchanged and adds one packet tensor per packet, of degree at most $2L$.
--
--   So near an easy point $F$ is still a sum of products of 64 contractions of much smaller networks.
--
--   **Formalization Note** The node ring is $\mathbb Z_{(2)}[U]/(f)$ for any monic $f$ with $f$ mod $2$ irreducible. The congruence is in $\mathcal O$.
--
--   Differences from the source:
--   - reading: there are modes ξ and networks G_{g,β} → the defined modes and networks of the proofs of Lemmas A.12.1 and A.12.2; reason: Lemma A.18 uses "the networks of Lemma A.12"; the defined form implies the existential one
--   - reading: labels and packets of Lemma A.9, in the setting of a call → orientation, small groups, at most 3M/L packets and M ≥ LQ as hypotheses, and tables in O; reason: these are the facts the proof uses, and the page takes them from Lemma A.9
--   - generalization: f of degree 4λ → every monic f with f mod 2 irreducible, of any degree; reason: the paper picks one such f by search; degree 4λ is a special case
--   - reading: a node z_j ∈ O → a binary node ∑ b_k U^k; reason: these are the nodes defined on p.96
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.12, p.69; proof p.91

import Mathlib
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_Placement
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_BipNet_rewiring
import Definitions.Def_ContractionLemma_zoom
import Definitions.Def_ContractionLemma_Et
import Definitions.Def_ContractionLemma_NodeField
import Definitions.Def_ContractionLemma_Splitting_modeSet
import Definitions.Def_ContractionLemma_Splitting_childNet

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.12 (Splitting near an easy point)** — Gajulapalli, *The Contraction Lemma Beyond
ETH* (manuscript, sha256 049caea1…), p.69 (PDF p.72); proof p.91.

Let `G` be a bipartite network with `M` edges and tables in the node ring `O`, with labels and
packets as in Lemma A.9 (orientation, small groups, at most `3M/L` packets, `M ≥ LQ`), and
rewiring polynomial `F`. Fix `t ∈ E \ {−L}` of level `i`, a precision `p′` and a node `z_j ∈ O`.
The modes `ξ` (each with weight `w_ξ ≥ 1`) satisfy:
(a) there are at most `6M/D_i` modes of each weight, `D_i = L/2^i`;
(b) with the networks `G_{g,β}` (one per level-`i` group `g`),
`F(t + αz_j) ≡ ∑_{β : ∑_ξ w_ξ β_ξ < p′} ∏_g Z(G_{g,β}) (mod 2^{p′})`;
(c) each `G_{g,β}` is bipartite with fewer than `M/8` edges; it keeps the old tables of `g`
unchanged and adds one packet tensor per packet, of degree at most `2L`.

**Formalization Note.** The modes and the networks are the constructions of the proofs of
Lemmas A.12.1 and A.12.2 (`Splitting.modeSet`, `Splitting.childNet`); bipartiteness, the
unchanged old tables and "one packet tensor per packet" hold by construction. Congruence is in
`O` (`CongrO`). The node ring is `ℤ_{(2)}[U]/(f)` for any monic `f` with `f mod 2` irreducible
(the paper takes `deg f = 4λ`). -/
theorem lemma_A_12_splitting_near_easy_point {U W E : Type*} [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (f : ℤ[X]) (dg : ℕ) (hf : IsNodePoly f dg) (a : ℕ) (G : BipNet U W E (NodeField f))
    (hrowO : ∀ u zz, IsInO f (G.rowTable u zz)) (hcolO : ∀ w zz, IsInO f (G.colTable w zz))
    (pk : Packing U W E a) (hor : pk.Orientation G.rowOf G.colOf)
    (hsm : pk.SmallGroups G.rowOf G.colOf) (hfew : pk.FewPackets)
    (hLQ : 2 ^ a * 64 ^ (2 * a) ≤ Fintype.card E)
    (t : ℤ) (ht : t ∈ easyPts a) (htL : t ≠ -(2 ^ a : ℤ)) (i : ℕ) (hi : i = padicValInt 2 t)
    (p' : ℕ) (b : Fin f.natDegree → Bool) :
    (∀ ξ : Splitting.Mode G pk i p', 1 ≤ Splitting.weight ξ) ∧
    (∀ w : ℕ, ((Finset.univ.filter fun ξ : Splitting.Mode G pk i p' =>
        Splitting.weight ξ = w).card : ℝ) ≤ 6 * Fintype.card E / 2 ^ (a - i)) ∧
    CongrO f p' ((G.rewiring pk.toPlacement).eval (Splitting.evalPt a t (binNode f b)))
      (∑ β ∈ Splitting.survivors G pk i p',
        ∏ g : Fin 64, (Splitting.childNet G pk t i (binNode f b) p' g β).Z) ∧
    (∀ (β : Splitting.Mode G pk i p' → ℕ) (g : Fin 64),
      (Fintype.card (Splitting.Bits G pk i g) : ℝ) < Fintype.card E / 8 ∧
      ∀ P, (Splitting.childNet G pk t i (binNode f b) p' g β).colDeg P ≤ 2 * 2 ^ a) := by sorry

end ContractionLemma
