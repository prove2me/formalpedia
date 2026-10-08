-- Prove2me | Theorems.Thm_BasicPackArb_Main_eq_4
-- name    : BasicPackArb.Main.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:58.664598+00:00
-- url     : https://prove2.me/theorems/f6f199fb-eff3-4f34-8841-bc7c7e8dc52e
-- title:
--   (4), p. 5 — if Claim 2.4 fails, every bad arc uv enters a tight set X that dominates u
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots, $D=(V,A)$, and $M$ a matroid on $S$, with $\pi$ $M$-independent and $(D,S,\pi)$ $M$-connected. Assume that Claim 2.4 is false: for every bad arc $uv\in A$ and every $s\in S_u\setminus\mathrm{Span}_M(S_v)$, the digraph with roots $(D-uv,S',\pi')$ is **not** $M'$-connected, where $S'=S\cup\{s'\}$, $M'$ makes $s'$ parallel to $s$ and $\pi'$ places $s'$ at $v$. Then
--
--   $$\text{every bad arc }uv\text{ enters a tight set }X\text{ that dominates }u,\tag{4}$$
--
--   that is, there is $X\subseteq V$ with $uv\in\varrho_D(X)$, $\rho_D(X)=r_M(S)-r_M(S_X)$ and $S_u\subseteq\mathrm{Span}_M(S_X)$.
--
--   Statement (4) is the intermediate conclusion of the proof by contradiction of Claim 2.4.
--
--   **Formalization Note** The paper proves (4) under "Assume that the claim is false"; that assumption and the standing hypotheses of the sufficiency proof are binders. The extension $(D',S',\pi',M')$ is `D.deleteArc a`, `extPlacement D π a`, `extMatroid M s` on `Option S`. Tightness and $M$-connectedness are written additively in $\mathbb{N}_\infty$.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 5, (4) (in the proof of Claim 2.4)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

namespace BasicPackArb.Main

/-- (4) (p. 5), inside the proof of Claim 2.4, under the standing hypotheses of the sufficiency
proof (`π` is `M`-independent and `(D, S, π)` is `M`-connected) and the assumption that
Claim 2.4 is false: for every bad arc `a = uv ∈ A` and every `s ∈ S_u \ Span_M(S_v)`, the digraph
with roots `(D − uv, S', π')` is not `M'`-connected. Conclusion: every bad arc `uv` enters a tight
set `X` that dominates `u`. -/
theorem eq_4 {V Arc S : Type*} [Fintype V] [DecidableEq V] [DecidableEq Arc] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hind : MIndependent π M) (hconn : MConnected D π M)
    (hfalse : ∀ a ∈ D.arcs, ¬ IsGoodArc D π M a → ∀ s : S, π s = D.tail a →
      s ∉ Span M (π ⁻¹' {D.head a}) →
      ¬ MConnected (D.deleteArc a) (extPlacement D π a) (extMatroid M s)) :
    ∀ a ∈ D.arcs, ¬ IsGoodArc D π M a →
      ∃ X : Finset V, a ∈ D.enteringArcs X ∧ IsTight D π M X ∧
        Dominates π M X {D.tail a} := by sorry

end BasicPackArb.Main
