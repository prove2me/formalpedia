-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_18_one_call
-- name    : ContractionLemma.lemma_A_18_one_call
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:29.305122+00:00
-- url     : https://prove2.me/theorems/b6e39268-8813-47ba-bd1e-d2a30abcaa24
-- title:
--   Lemma A.18 — one call of the recursion
-- statement:
--   There are $s^*$ and $K$ depending only on $C$ such that the following holds for $s\ge s^*$. Consider a call at depth $d$ with $M>H$ and precision $p$: a bipartite network $G$ with tables in $\mathcal O$, with $M\le Cs8^{-d}$ edges and maximum degree at most $\Delta$, $p\le 47Cs2^{a_{d-1}}$, labels and packets as in Lemma A.9 with $a=a_d$, and $D^*+1$ distinct nodes, $D^*=M(2L-1)$. For each easy point $t$ with $m_t>0$ and each node $z_j$, let $G_{g,\beta}$ be the networks of Lemma A.12 at $T=t+\alpha z_j$ with precision $p_t$, and let $v_{t,j}$ be any element of $\mathcal O$ with
--
--   $$
--   v_{t,j}\equiv\sum_{\beta:\ \sum_\xi w_\xi\beta_\xi<p_t}\ \prod_g Z(G_{g,\beta})\pmod{2^{p_t}}.
--   $$
--
--   Then:
--
--   1. (correctness) $Z(G)\equiv\sum_t\sum_{j=0}^{D^*}\Omega_{t,j}v_{t,j}\pmod{2^p}$;
--   2. (children) each $G_{g,\beta}$ is bipartite, with fewer than $M/8$ edges and maximum degree at most $\Delta$;
--   3. (branching) for each pair $(t,j)$, the number of $\beta$ is at most $\exp(KM/\sqrt{u_d})$.
--
--   This is the whole recursive step in one formula.
--
--   **Formalization Note** The congruence is in $\mathcal O$, with the weights computed in $\mathbb Q[U]/(f)$: the difference of the two sides lies in $2^p\mathcal O$. $f$ is monic of degree $4\lambda$ with $f$ mod $2$ irreducible.
--
--   Differences from the source:
--   - reading: a call at depth d with precision p → H < M ≤ C s 8^{−d}, maximum degree ≤ ∆, tables in O, p ≤ 47 C s 2^{a_{d−1}}, and the packing of Lemma A.9 at a = a_d; reason: these are the invariants of an admissible call (p.78) and the steps of Eval
--   - encoding: the number of β is exp(O(M/√u_d)) → an upper bound exp(K M/√u_d) with K fixed before s and depending only on C; reason: O(·) made explicit; the proof gives an upper bound
--   - reading: D∗ + 1 nodes z_0, …, z_{D∗} in O with pairwise differences that are units → an injective family of D∗ + 1 binary nodes ∑ b_k U^k, with f monic of degree 4λ and f mod 2 irreducible; reason: these are the nodes and the ring of p.96; distinct binary nodes differ by units
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.18, pp.76–77; proof p.97

import Mathlib
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
import Definitions.Def_ContractionLemma_Omega

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.18 (One call)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), pp.76–77 (PDF pp.79–80); proof p.97.

Fix the constant `C > 0` of the reduction. There are `s*` and `K` (depending only on `C`) such
that for `s ≥ s*` and a call at depth `d` — a bipartite network `G` with tables in `O`, with
`H < M ≤ C s 8^{−d}` edges and maximum degree at most `∆`, at precision `p` — with labels and
packets as in Lemma A.9 for `a = a_d`, the taper orders `q_i = h max(0, u_d − i)`,
`h = ⌈3M/u_d⌉`, `m_t = q_{v₂(t)}`, the child precisions `p_t`, and `D* + 1 = M(2L − 1) + 1`
distinct binary nodes `z_j`: let `G_{g,β}` be the networks of Lemma A.12 at `T = t + αz_j` with
precision `p_t`, and let `v_{t,j}` be any elements of `O` with
`v_{t,j} ≡ ∑_{β : ∑ w_ξ β_ξ < p_t} ∏_g Z(G_{g,β}) (mod 2^{p_t})` for every easy point `t` with
`m_t > 0`. Then
(a) (correctness) `Z(G) ≡ ∑_t ∑_{j=0}^{D*} Ω_{t,j} v_{t,j} (mod 2^p)`;
(b) (children) each `G_{g,β}` is bipartite, with fewer than `M/8` edges and maximum degree at
most `∆`;
(c) (branching) for each pair `(t, j)` the number of `β` is at most `exp(K M/√u_d)`.

**Formalization Note.** "A call at depth `d` with precision `p`" carries the invariants of the
recursion: `M ≤ C s 8^{−d}`, maximum degree `≤ ∆ = ⌈s^{9/10}⌉`, tables in `O`, and
`p ≤ 47 C s 2^{a_{d−1}}` (Lemma A.17). The congruence is in `O` (`CongrO`); the weights
`Ω_{t,j}` are computed in `ℚ[U]/(f)`. The node ring is `ℤ_{(2)}[U]/(f)` with `f` monic of
degree `4λ` and `f mod 2` irreducible. `exp(O(M/√u_d))` is `exp(K M/√u_d)` with `K` fixed
before `s`. -/
theorem lemma_A_18_one_call (C : ℝ) (hC : 0 < C) :
    ∃ (sStar : ℕ) (K : ℝ), ∀ s ≥ sStar, ∀ (d p : ℕ) {U W E : Type*} [Fintype U] [DecidableEq U]
      [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E] (f : ℤ[X]),
      IsNodePoly f (4 * lam s) →
      ∀ (G : BipNet U W E (NodeField f)),
      (∀ u zz, IsInO f (G.rowTable u zz)) → (∀ w zz, IsInO f (G.colTable w zz)) →
      leafH s < Fintype.card E → (Fintype.card E : ℝ) ≤ C * s / 8 ^ d →
      (∀ u, G.rowDeg u ≤ degCap s) → (∀ w, G.colDeg w ≤ degCap s) →
      (p : ℝ) ≤ 47 * C * s * 2 ^ aPrev s d →
      ∀ (pk : Packing U W E (aSlot s d)), pk.Orientation G.rowOf G.colOf →
      pk.SmallGroups G.rowOf G.colOf → pk.FewPackets →
      ∀ (nodes : Fin (Fintype.card E * (2 * 2 ^ aSlot s d - 1) + 1) → Fin f.natDegree → Bool),
      Function.Injective nodes →
      ∀ (v : ℤ → Fin (Fintype.card E * (2 * 2 ^ aSlot s d - 1) + 1) → NodeField f),
      (∀ t ∈ easyPts (aSlot s d),
        0 < orderAt (fun i => taperH (Fintype.card E) (uLev s d) * (uLev s d - i)) t →
        ∀ j, IsInO f (v t j) ∧
          CongrO f (childPrec s d (Fintype.card E) (padicValInt 2 t) p) (v t j)
            (∑ β ∈ Splitting.survivors G pk (padicValInt 2 t)
                (childPrec s d (Fintype.card E) (padicValInt 2 t) p),
              ∏ g : Fin 64, (Splitting.childNet G pk t (padicValInt 2 t) (binNode f (nodes j))
                (childPrec s d (Fintype.card E) (padicValInt 2 t) p) g β).Z)) →
      CongrO f p G.Z
        (∑ t ∈ (easyPts (aSlot s d)).filter (fun t =>
            0 < orderAt (fun i => taperH (Fintype.card E) (uLev s d) * (uLev s d - i)) t),
          ∑ j, Omega f (aSlot s d)
            (fun i => taperH (Fintype.card E) (uLev s d) * (uLev s d - i)) t
            (fun k => binNode f (nodes k)) j * v t j) ∧
      (∀ t ∈ easyPts (aSlot s d),
        0 < orderAt (fun i => taperH (Fintype.card E) (uLev s d) * (uLev s d - i)) t →
        ∀ j β (g : Fin 64),
          (Fintype.card (Splitting.Bits G pk (padicValInt 2 t) g) : ℝ) < Fintype.card E / 8 ∧
          (∀ x, (Splitting.childNet G pk t (padicValInt 2 t) (binNode f (nodes j))
              (childPrec s d (Fintype.card E) (padicValInt 2 t) p) g β).rowDeg x ≤ degCap s) ∧
          (∀ P, (Splitting.childNet G pk t (padicValInt 2 t) (binNode f (nodes j))
              (childPrec s d (Fintype.card E) (padicValInt 2 t) p) g β).colDeg P ≤ degCap s)) ∧
      (∀ t ∈ easyPts (aSlot s d),
        0 < orderAt (fun i => taperH (Fintype.card E) (uLev s d) * (uLev s d - i)) t →
        ((Splitting.survivors G pk (padicValInt 2 t)
            (childPrec s d (Fintype.card E) (padicValInt 2 t) p)).card : ℝ) ≤
          Real.exp (K * Fintype.card E / Real.sqrt (uLev s d))) := by sorry

end ContractionLemma
