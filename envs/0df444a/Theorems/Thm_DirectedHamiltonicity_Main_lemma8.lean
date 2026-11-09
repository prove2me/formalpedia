-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_lemma8
-- name    : DirectedHamiltonicity.Main.lemma8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:48.085861+00:00
-- url     : https://prove2.me/theorems/e7744b75-b27d-4a26-a8c9-2abe1e6ffe4b
-- title:
--   Lemma 8 — $h(y)=\sum_{X\subseteq I}\det L_s(H_X^A,p)$ (corrected: added arcs are loopless)
-- statement:
--   Let $H$ be a loopless directed multigraph on a finite vertex set $V$ with distinct vertices $s,t$, no arc entering $s$ and no arc leaving $t$, and let $p:E(H)\to\mathbb F_2[y]$. Put
--   $$h(y)=\sum_{P\in\mathcal P_{s,t}(H)}\prod_{e\in P}p(e),\qquad I=V\setminus\{s,t\}.$$
--   Let $A$ be any finite set of additional arcs leaving $t$, **each with head different from $t$**, and extend $p$ arbitrarily to $A$. For $X\subseteq I$ let $H_X^A$ be obtained from $H$ by deleting the arcs leaving vertices of $I\setminus X$ and adding $A$. Then
--   $$h(y)=\sum_{X\subseteq I}\det L_s(H_X^A,p).$$
--
--   The correction excludes added loops $t\to t$: with them the printed statement is false. Take $V=\{s,t\}$, $H=\{s\to t\}$ with label $1$ and $A=\{t\to t\}$ with label $1$; every assumption holds, $I=\varnothing$ and $h(y)=1$, but the only term is $\det[1+1]=0$ over $\mathbb F_2[y]$. The algorithm adds only arcs $t\to i$ with $i\in I$, so Proposition 4 and Theorem 1 are unaffected. The lemma lets random added arcs make most of the $2^{n-2}$ determinants vanish.
--
--   Differences from the source:
--   - correction: A is any set of additional arcs leaving t → every added arc has tail t and head different from t; reason: with an added loop t→t the statement is false: V = {s,t}, H = {s→t} labelled 1, A = {t→t} labelled 1 gives h = 1 but the only term X = ∅ is det[1+1] = 0 over F₂[y] (checked sorry-free in Solutions/verification/DirectedHamiltonicity_Main_Checks.lean)
--   - generalization: p(e) = y^{w(e)} on the arcs of H, with parallel arcs of H carrying distinct weights (§4.1 normalization) → arbitrary labels p : E(H) → F₂[y] and no assumption on parallel arcs; reason: the source case is p = y^w on a normalized H; the inclusion–exclusion identity holds for any labels
--   - encoding: H after the normalization of §4.1 (no loops, no arcs entering s, no arcs leaving t), s ≠ t → hypotheses hloop, hs, ht, hst; reason: the standing assumptions of the section written as binders
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.9 / printed p.8, Lemma 8 (setting PDF p.8 / printed p.7)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum

namespace DirectedHamiltonicity.Main

open Multidigraph

open Polynomial

open Classical in
/-- Lemma 8, PDF p.9 / printed p.8 (corrected: the added arcs are not loops). Let `H` be a loopless
directed multigraph with distinct vertices `s, t`, no arc entering `s` and no arc leaving `t`, with
labels `p : E(H) → 𝔽₂[y]`, and let `h(y) = ∑_{P ∈ 𝒫_{s,t}(H)} ∏_{e ∈ P} p(e)`. Let `A` be any finite
set of additional arcs leaving `t`, each with head different from `t`, with arbitrary labels
`p_A : A → 𝔽₂[y]`. For `X ⊆ I = V ∖ {s,t}` let `H_X^A` be `H_X` (delete the arcs leaving `I ∖ X`)
together with `A`. Then `h(y) = ∑_{X ⊆ I} det L_s(H_X^A, p)`. -/
theorem lemma8 {V E EA : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype EA] [DecidableEq EA]
    (H : Multidigraph V E) (s t : V) (hst : s ≠ t) (hloop : H.Loopless)
    (hs : ∀ e, H.head e ≠ s) (ht : ∀ e, H.tail e ≠ t) (p : E → (ZMod 2)[X])
    (A : Multidigraph V EA) (hAt : ∀ a, A.tail a = t) (hAloop : ∀ a, A.head a ≠ t)
    (pA : EA → (ZMod 2)[X]) :
    H.hamPathPoly p s t =
      ∑ X : Finset (Internal s t),
        (((H.subX s t X).addArcs A).reducedLaplacian (Sum.elim (fun e => p e.1) pA) s).det := by sorry

end DirectedHamiltonicity.Main
