-- Prove2me | Theorems.Thm_BasicPackArb_Main_lifting_step
-- name    : BasicPackArb.Main.lifting_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:18.267984+00:00
-- url     : https://prove2.me/theorems/32c8f20e-0bcb-4594-bd80-19213c20808d
-- title:
--   §2, p. 5, lifting step — π′ is M′-independent and an M′-basic packing of (D−uv, S′, π′) lifts to (D, S, π)
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots, $D=(V,A)$, and $M$ a matroid on $S$ with $\pi$ $M$-independent. Let $uv\in A$ be a bad arc and $s\in S_u\setminus\mathrm{Span}_M(S_v)$. Let $D'=D-uv$, let $S'=S\cup\{s'\}$ with a new element $s'$, let $M'$ be the matroid on $S'$ obtained from $M$ by making $s'$ parallel to $s$, and let $\pi'$ extend $\pi$ by placing $s'$ at $v$. Then
--
--   1. $\pi'$ is $M'$-independent; and
--   2. if $(D',S',\pi')$ has an $M'$-basic packing of arborescences, then $(D,S,\pi)$ has an $M$-basic packing of arborescences.
--
--   This is the induction step of the proof of sufficiency: removing a bad arc and adding a parallel root at its head reduces the theorem to Claim 2.4.
--
--   **Formalization Note** The step is unnumbered in the paper. It is stated without the induction hypothesis: part 2 takes the packing of $(D',S',\pi')$ as a hypothesis. $S'$ is `Option S`, $s'$ = `none`, $M'$ = `extMatroid M s` (the comap of $M$ along $o\mapsto o.\mathrm{getD}\ s$), $\pi'$ = `extPlacement D π a`, $D'$ = `D.deleteArc a`. The standing hypothesis of the sufficiency proof used here ($\pi$ $M$-independent) is a binder; $M$-connectedness is not needed by this step and is not assumed.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 5, §2, proof of sufficiency in Theorem 1.6 (paragraphs "For a bad arc uv ∈ A …" and "By choice of s …")

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

namespace BasicPackArb.Main

/-- The lifting step of the sufficiency proof (§2, p. 5), with its standing hypothesis that `π` is
`M`-independent. For a bad arc `a = uv ∈ A` and `s ∈ S_u \ Span_M(S_v)`, let `D' = D − uv`,
`S' = S ∪ {s'}` (`Option S`, `s' = none`), `M'` the matroid on `S'` with `s'` parallel to `s`,
and `π'` placing `s'` at `v`. Then (i) `π'` is `M'`-independent, and (ii) every `M'`-basic
packing of arborescences in `(D', S', π')` yields an `M`-basic packing of arborescences in
`(D, S, π)`. -/
theorem lifting_step {V Arc S : Type*} [Fintype V] [DecidableEq V] [DecidableEq Arc] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hind : MIndependent π M) (a : Arc) (ha : a ∈ D.arcs) (hbad : ¬ IsGoodArc D π M a)
    (s : S) (hsu : π s = D.tail a) (hsv : s ∉ Span M (π ⁻¹' {D.head a})) :
    MIndependent (extPlacement D π a) (extMatroid M s) ∧
      ((∃ T' : Option S → Arborescence (D.deleteArc a),
          IsBasicPacking (D.deleteArc a) (extPlacement D π a) (extMatroid M s) T') →
        ∃ T : S → Arborescence D, IsBasicPacking D π M T) := by sorry

end BasicPackArb.Main
