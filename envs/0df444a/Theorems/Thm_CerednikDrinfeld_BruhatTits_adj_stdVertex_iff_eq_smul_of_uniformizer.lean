-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer
-- name    : CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/5354dff0-ee7a-5c05-a71a-5242fcf4fa66
-- title:
--   Neighbours of the standard vertex of the Bruhat–Tits tree
-- statement:
--   Let $R$ be a discrete valuation domain and $K_0$ a field that is a fraction field of $R$ (as an $R$-algebra, via `IsFractionRing`), and let $\varpi \in R$ be irreducible. Let $n \in \mathrm{GL}_2(K_0)$ be an element whose underlying matrix is $!![1,0;0,\varpi]$ (the image of $\varpi$ under the algebra map to $K_0$), and let $s : R \to \mathrm{GL}_2(K_0)$ be a family whose underlying matrices are $!![t,1;1,0]$ for $t \in R$. The vertices in question are homothety classes of full $R$-lattices in $K_0^2$, `stdVertex` being the class of the lattice of vectors all of whose coordinates lie in the image of $R$, and `BruhatTits.tree` is the simple graph obtained from the relation `VertRel`: two classes are adjacent when they are distinct and, in one order or the other, they admit full-lattice representatives $L$, $L'$ satisfying `AdjacentLattice L L'`. The assertion is the conjunction of five statements: `stdVertex` is adjacent to $n \cdot$`stdVertex`; each $s_t$ fixes `stdVertex`; every neighbour $y$ of `stdVertex` equals $n \cdot$`stdVertex` or $(s_t n) \cdot$`stdVertex` for some $t \in R$; $(s_t n) \cdot$`stdVertex` $= (s_{t'} n) \cdot$`stdVertex` if and only if $\varpi \mid t - t'$; and $n \cdot$`stdVertex` is never equal to $(s_t n) \cdot$`stdVertex`.
--
--   This is the local description of the Bruhat–Tits tree of $\mathrm{GL}_2$ over a discretely valued field at the standard vertex: its neighbours are the lattices strictly between $\varpi R^2$ and $R^2$, parametrised by $n$ together with the classes $s_t n$ for $t$ running over $R/\varpi$, so that the standard vertex has $q+1$ neighbours when the residue field has $q$ elements. It is used in the Čerednik–Drinfeld and Mumford-curve part of the development, for instance in the analysis of principal divisors, theta functions and periods on Mumford quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (n : GL (Fin 2) K₀) (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, algebraMap R K₀ ϖ])
    (s : R → GL (Fin 2) K₀) (hs : ∀ t : R, (s t : Matrix (Fin 2) (Fin 2) K₀) = !![algebraMap R K₀ t, 1; 1, 0]) :
    (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) (n • LT.LatticeTree.stdVertex R K₀) ∧
    (∀ t : R, s t • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀) ∧
    (∀ y : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y →
      y = n • LT.LatticeTree.stdVertex R K₀ ∨ ∃ t : R, y = (s t * n) • LT.LatticeTree.stdVertex R K₀) ∧
    (∀ t t' : R, (s t * n) • LT.LatticeTree.stdVertex R K₀ = (s t' * n) • LT.LatticeTree.stdVertex R K₀ ↔ ϖ ∣ t - t') ∧
    (∀ t : R, n • LT.LatticeTree.stdVertex R K₀ ≠ (s t * n) • LT.LatticeTree.stdVertex R K₀) := by sorry
