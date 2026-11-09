-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_kikuchi_edge_identity
-- name    : BinaryThreeLCC.Main.kikuchi_edge_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:47.683443+00:00
-- url     : https://prove2.me/theorems/8158602e-c0f5-4f85-91f0-e03d85c4c034
-- title:
--   Observation 5.2 — vector label of a Kikuchi edge
-- statement:
--   Let $\mathcal H$ be a tuple system with distinct label pairs and uniqueness at each $(u,a)$, labelled by vectors $v_u,w_a$ in an arbitrary $\mathbb F_2$-vector space, satisfying its parity equations. Construct the real and fake tuple multiset $\mathcal T$ exactly as on printed p.13. For a palette $\mathcal C\subseteq\Omega$ and an integer $r\ge1$, form the ordered $r$-chain Kikuchi graph. Put
--
--   $$v_{(\vec a,u)}=v_u+\sum_{j=1}^r w_{a_j},\qquad
--   v_{\vec b}=\sum_{j=1}^r w_{b_j}.$$
--
--   For each edge copy of colour $i$ between $(\vec a,u)$ and $\vec b$,
--
--   $$v_{(\vec a,u)}+v_{\vec b}=v_i.$$
--
--   All coordinate repetitions and tuple multiplicities are retained. This is the vector identity used to exclude odd-coloured cycles when the palette vectors are independent.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - generalization: the surrounding proof chooses independent palette vectors and an expanding Eulerian flattening → the identity is stated for every palette, without independence, expansion or balance assumptions; reason: each individual chain identity uses only its tuple parity relations; all source instances specialize directly
--   - encoding: one edge per chain with tuple multiplicity → a finite type of chains choosing labelled tuple copies; reason: copies remain distinct even when their labels, endpoints and colours agree
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Observation 5.2, printed p. 14, PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Kikuchi

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Observation 5.2, for every edge copy, real or fake. -/
theorem kikuchi_edge_identity {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    {W : Type*} [AddCommGroup W] [Module Bit W]
    (H : TupleSystem Ω Λ) (v : Ω → W) (w : Λ → W) (hparity : TupleParity H v w)
    (C : Finset Ω) (r : ℕ) (hr : 1 ≤ r) (e : Chain H C r) :
    leftVector v w (chainLeft e) + rightVector w (chainRight e) =
      v (chainHead e).val := by sorry

end BinaryThreeLCC.Main
