-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
-- name    : CerednikDrinfeld.BruhatTits.exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/9be69b70-4c1a-5af2-9b85-ee7391e4e763
-- title:
--   Every dart of the Bruhat–Tits tree is a GL₂-translate of a standard dart
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, with field of fractions $K_0$ (via an algebra map making $K_0$ a localisation of $R$ at its nonzero elements), and let $\varpi \in R$ be irreducible. Let $n \in GL_2(K_0)$ be an element whose underlying matrix is $!![1,0;0,\varpi]$, and let $s : R \to GL_2(K_0)$ assign to each $t \in R$ an element with underlying matrix $!![t,1;1,0]$. Let $d$ be a dart of the graph [`CerednikDrinfeld.BruhatTits.tree R K₀`](def/CerednikDrinfeld_BruhatTitsTree.html#L83), that is, an ordered pair of adjacent vertices $d.\mathrm{fst}, d.\mathrm{snd}$, the vertices being homothety classes of full $R$-lattices in $K_0^2$ and adjacency being the symmetrisation (`SimpleGraph.fromRel`) of the relation that the two classes have representatives $L, L'$ with `AdjacentLattice L L'`. The assertion is that there exist $g \in GL_2(K_0)$ and $t \in R$ with $g \cdot v_0 = d.\mathrm{fst}$ and $(g\, s_t\, n) \cdot v_0 = d.\mathrm{snd}$, where $v_0 =$ [`LT.LatticeTree.stdVertex R K₀`](def/LatticeTreeOrbital.html#L358) is the class of the lattice of vectors in $K_0^2$ both of whose coordinates lie in the image of $R$.
--
--   This is the standard transitivity statement for the action of $GL_2(K_0)$ on the oriented edges of the Bruhat–Tits tree of $GL_2$ over a discretely valued field: $GL_2(K_0)$ is transitive on vertices and the stabiliser of the standard vertex moves the standard neighbour $n v_0$ onto each of the remaining neighbours $s_t n v_0$. It is used in the Čerednik–Drinfeld part of the development, in the analysis of path cycles and of the valuation of theta functions on $\Omega$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd.lean

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.BruhatTits.exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (n : GL (Fin 2) K₀) (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, algebraMap R K₀ ϖ])
    (s : R → GL (Fin 2) K₀) (hs : ∀ t : R, (s t : Matrix (Fin 2) (Fin 2) K₀) = !![algebraMap R K₀ t, 1; 1, 0])
    (d : (BruhatTits.tree R K₀).Dart) :
    ∃ (g : GL (Fin 2) K₀) (t : R),
      g • LT.LatticeTree.stdVertex R K₀ = d.fst ∧ (g * s t * n) • LT.LatticeTree.stdVertex R K₀ = d.snd := by sorry
