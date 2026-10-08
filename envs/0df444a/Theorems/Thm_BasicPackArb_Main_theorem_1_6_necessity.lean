-- Prove2me | Theorems.Thm_BasicPackArb_Main_theorem_1_6_necessity
-- name    : BasicPackArb.Main.theorem_1_6_necessity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:59.71599+00:00
-- url     : https://prove2.me/theorems/0b36e455-ff20-48bf-abd0-a341ab09f646
-- title:
--   Theorem 1.6, necessity — an M-basic packing of arborescences forces π M-independent and (D,S,π) M-connected
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots, $D=(V,A)$ finite, and $M$ a matroid on the finite set $S$. If $(D,S,\pi)$ has an $M$-basic packing of arborescences $(T_s)_{s\in S}$, then
--
--   1. $\pi$ is $M$-independent: $S_v$ is independent in $M$ for every vertex $v$; and
--   2. $(D,S,\pi)$ is $M$-connected:
--   $$\rho_D(X)\ \ge\ r_M(S)-r_M(S_X)\qquad\text{for every non-empty }X\subseteq V.$$
--
--   This is the "only if" direction of Theorem 1.6, proved separately at the start of §2.
--
--   **Formalization Note** The packing is a family `T : S → Arborescence D` satisfying `IsBasicPacking`; $M$-connectedness is stated additively, $r_M(S)\le\rho_D(X)+r_M(S_X)$, in $\mathbb{N}_\infty$. The matroid's ground set is assumed to be the whole root type.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 4, §2, proof of necessity in Theorem 1.6

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph

namespace BasicPackArb.Main

/-- Necessity in Theorem 1.6 (§2, p. 4): if `(D, S, π)` has an `M`-basic packing of arborescences,
then `π` is `M`-independent and `(D, S, π)` is `M`-connected. -/
theorem theorem_1_6_necessity {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hT : ∃ T : S → Arborescence D, IsBasicPacking D π M T) :
    MIndependent π M ∧ MConnected D π M := by sorry

end BasicPackArb.Main
