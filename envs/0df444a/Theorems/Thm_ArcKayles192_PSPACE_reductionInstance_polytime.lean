-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_reductionInstance_polytime
-- name    : ArcKayles192.PSPACE.reductionInstance_polytime
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:45.865855+00:00
-- url     : https://prove2.me/theorems/ab82913b-bcbd-476a-8b71-51d139486157
-- title:
--   The explicit Pos CNF to Arc Kayles instance map is polynomial-time computable
-- statement:
--   There is a deterministic multi-stack Turing machine which, on the binary encoding of a Pos CNF instance $\varphi$, computes the binary adjacency-matrix encoding of `reductionInstance` $\varphi$ in polynomial time.
--
--   For nonempty $\varphi$, the machine duplicates $C_1$ if needed and writes the matrix of $G_{\mathrm{oddPad}(\varphi)}$ in the explicit vertex order $s,t,A,B,V,T,F,Y,Z$. For the empty conjunction it writes the fixed encoding of $K_2$. The graph has $O(n+m)$ vertices, so its $O((n+m)^2)$ adjacency bits can be enumerated in polynomial time by evaluating the finite edge rules of the construction.
--
--   **Formalization Note.** Polynomial time is Mathlib’s `Turing.TM2ComputableInPolyTime`, with the published `PosCNF.enc` input encoding and `GraphInstance.enc` output encoding.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.5 (duplicate one clause when m is even), p.6 (Construction and 'Graph G has ... O(n+m) vertices, and can be built in polynomial time').

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_ArcKayles192_PSPACE_ReductionInstance

/-- Polynomial-time computability of the explicit reduction map: on the incidence-matrix encoding
of `φ`, a multi-stack Turing machine outputs the adjacency-matrix encoding of `reductionInstance φ`
in time polynomial in the input length. This includes the odd-clause padding and the fixed one-edge
output for the empty conjunction. -/
theorem ArcKayles192.PSPACE.reductionInstance_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime PosCNF.enc GraphInstance.enc reductionInstance) := by sorry
