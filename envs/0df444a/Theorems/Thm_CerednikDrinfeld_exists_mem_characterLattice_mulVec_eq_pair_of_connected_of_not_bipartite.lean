-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite
-- name    : CerednikDrinfeld.exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/14313779-e1ef-5bab-b9d6-19f7961658db
-- title:
--   Joint degeneracy push-forward is onto degree-zero divisors
-- statement:
--   Let $E$ and $V$ be finite types, $V$ with decidable equality, and let $a, b \colon E \to V$ be two maps, so that each $e \in E$ is thought of as an edge joining $a(e)$ to $b(e)$. Assume three hypotheses: (i) for every $e$ there is $e'$ with $a(e') = b(e)$ and $b(e') = a(e)$; (ii) every $P \subseteq V$ such that $a(e) \in P \iff b(e) \in P$ for all $e$ is either empty or all of $V$; (iii) for every nonempty $P \subseteq V$ there is an edge $e$ with $a(e) \in P \iff b(e) \in P$, i.e. an edge having both or neither of its endpoints in $P$. For a map $f \colon E \to V$ let `degeneracyMatrix` $f$ be the $V \times E$ matrix over $\mathbb{Z}$ with entry $1$ at $(v,e)$ when $f(e) = v$ and $0$ otherwise, and let `characterLattice` of a finite type be the kernel of the sum-of-coordinates linear form on integer-valued functions on it. The conclusion: for all $x, y \colon V \to \mathbb{Z}$ with $\sum_{v} x(v) = 0$ and $\sum_v y(v) = 0$ there exists $D \colon E \to \mathbb{Z}$ with $\sum_e D(e) = 0$ such that for every $v$, $\sum_{e : a(e) = v} D(e) = x(v)$ and $\sum_{e : b(e) = v} D(e) = y(v)$.
--
--   This is the purely combinatorial half of the surjectivity statement for the degeneracy map on character groups of the component group of a Jacobian at a prime of multiplicative reduction (Ribet, Theorem 3.15): conditions (i)–(iii) express symmetry, connectedness and non-bipartiteness of the multigraph given by $a$ and $b$, and the conclusion says that the joint push-forward $(a_*, b_*)$ carries degree-zero divisors on edges onto pairs of degree-zero divisors on vertices. It is used by [`ModularCurve.SSLevelDatum.exists_mem_characterLattice_degeneracyMatrix_mulVec_eq_pair`](thm.html#ModularCurve.SSLevelDatum.exists_mem_characterLattice_degeneracyMatrix_mulVec_eq_pair), where $E$ and $V$ come from supersingular points with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_Ribbon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem CerednikDrinfeld.exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] (a b : E → V)
    (hsymm : ∀ e : E, ∃ e' : E, a e' = b e ∧ b e' = a e)
    (hconn : ∀ P : Set V, (∀ e : E, a e ∈ P ↔ b e ∈ P) → P = ∅ ∨ P = Set.univ)
    (hodd : ∀ P : Set V, P.Nonempty → ∃ e : E, (a e ∈ P ↔ b e ∈ P))
    (x y : V → ℤ) (hx : x ∈ characterLattice V) (hy : y ∈ characterLattice V) :
    ∃ D : E → ℤ, D ∈ characterLattice E ∧
      (CerednikDrinfeld.degeneracyMatrix a).mulVec D = x ∧
      (CerednikDrinfeld.degeneracyMatrix b).mulVec D = y := by sorry
