-- Prove2me | Theorems.Thm_BasicPackArb_Main_claim_2_2_a
-- name    : BasicPackArb.Main.claim_2_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:00.602505+00:00
-- url     : https://prove2.me/theorems/507d7126-e6c7-49ba-8d77-0a7fffede38f
-- title:
--   Claim 2.2 (a) — two tight sets sharing a vertex uncross: $X\cap Y$, $X\cup Y$ tight and $r_M$ modular on $S_X,S_Y$
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots and $M$ a matroid on $S$, and suppose $(D,S,\pi)$ is $M$-connected. Let $X$ be a tight set and $v$ a vertex of $X$. If $Y$ is a tight set that contains $v$, then $X\cap Y$ and $X\cup Y$ are tight and
--   $$r_M(S_X\cap S_Y)+r_M(S_X\cup S_Y)=r_M(S_X)+r_M(S_Y).$$
--
--   A set $X$ is tight when $\rho_D(X)=r_M(S)-r_M(S_X)$, i.e. condition (3) of $M$-connectedness holds with equality. Part (a) is the uncrossing property of intersecting tight sets used throughout §2.
--
--   **Formalization Note** The hypotheses are the claim's preamble ($M$-connected, $X$ tight, $v\in X$) and part (a)'s own ($Y$ tight, $v\in Y$). Tightness is written additively in $\mathbb{N}_\infty$; $S_X\cap S_Y$ and $S_X\cup S_Y$ are the preimages $\pi^{-1}(X)\cap\pi^{-1}(Y)$ and $\pi^{-1}(X)\cup\pi^{-1}(Y)$.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 4, Claim 2.2 (a)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

namespace BasicPackArb.Main

/-- Claim 2.2 (a) (p. 4). Suppose `(D, S, π)` is `M`-connected, `X` is a tight set and `v ∈ X`.
If `Y` is a tight set containing `v`, then `X ∩ Y` and `X ∪ Y` are tight and
`r_M(S_X ∩ S_Y) + r_M(S_X ∪ S_Y) = r_M(S_X) + r_M(S_Y)`. -/
theorem claim_2_2_a {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hconn : MConnected D π M) (X : Finset V) (hX : IsTight D π M X) (v : V) (hvX : v ∈ X)
    (Y : Finset V) (hY : IsTight D π M Y) (hvY : v ∈ Y) :
    IsTight D π M (X ∩ Y) ∧ IsTight D π M (X ∪ Y) ∧
      M.eRk (π ⁻¹' (X : Set V) ∩ π ⁻¹' (Y : Set V)) + M.eRk (π ⁻¹' (X : Set V) ∪ π ⁻¹' (Y : Set V))
        = M.eRk (π ⁻¹' (X : Set V)) + M.eRk (π ⁻¹' (Y : Set V)) := by sorry

end BasicPackArb.Main
