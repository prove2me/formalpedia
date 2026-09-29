-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
-- name    : CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/53410602-bda8-56a4-9c0e-961d4c68a35b
-- title:
--   Primitive integral g with det g=uvarpi^k moves [R²] exactly k
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, $K$ a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $\varpi \in R$ be irreducible. Let $g$ be an element of the general linear group $\mathrm{GL}_2(K)$, and suppose that every entry $g_{ij}$ of the underlying $2\times 2$ matrix over $K$ is an integer for the localisation, i.e. lies in the image of $R$; suppose further that for some natural number $k$ and some unit $u \in R^\times$ one has $\det g = \mathrm{algebraMap}_{R,K}(u)\cdot \mathrm{algebraMap}_{R,K}(\varpi)^k$, and that some entry $g_{ij}$ is the image of a unit of $R$. The assertion is that the graph distance, in the Bruhat–Tits tree [`CerednikDrinfeld.BruhatTits.tree R K`](def/CerednikDrinfeld_BruhatTitsTree.html#L83) — the simple graph on the set of homothety classes of full $R$-lattices in $K^2$ whose edges come from the relation that the two classes admit representatives $L$, $L'$ satisfying `AdjacentLattice L L'` — between the class `stdVertex` of the standard lattice $\{v \in K^2 : v_i \text{ integral for all } i\}$ and its translate $g \cdot \mathrm{stdVertex}$, equals $k$.
--
--   This is the standard computation of the displacement of the standard vertex of the Bruhat–Tits tree of $\mathrm{GL}_2$ over a discrete valuation ring by an integral, primitive matrix: the elementary divisors of $g$ are $(\varpi^a,\varpi^b)$ with $a+b=k$ and, primitivity forcing $a=0$, the distance is $b-a=k$; the corresponding inequality $\le k$ for arbitrary integral $g$ is [`CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq`](thm.html#CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq), and without the unit-entry hypothesis equality fails, as $g=\varpi\cdot 1$ shows. It feeds the parity criterion for type-preserving elements and the computations on the $p$-adic upper half plane, in particular the identification of a valuation of a cross-ratio with a walk invariant in the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit.lean

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k)
    (hunit : ∃ i j : Fin 2, ∃ w : Rˣ, (g : Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K w) :
    (CerednikDrinfeld.BruhatTits.tree R K).dist (LT.LatticeTree.stdVertex R K)
      (g • LT.LatticeTree.stdVertex R K) = k := by sorry
