-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq
-- name    : CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/4b7cbbdf-2bb0-529f-94a5-0c4aba5b82fa
-- title:
--   Integral g with det g = uvarpi^k moves the standard vertex by at most k
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $\varpi \in R$ be irreducible. Let $g$ be an element of the general linear group $\mathrm{GL}_2(K)$ (as a group of $2\times 2$ matrices indexed by `Fin 2`) all of whose entries $g_{ij}$ are integers over $R$ in the localisation sense, i.e. lie in the image of the algebra map $R \to K$. Suppose that for some natural number $k$ and some unit $u \in R^\times$ one has $\det g = u\,\varpi^{k}$ in $K$ (images under $R \to K$). The conclusion bounds the graph distance, in the graph [`CerednikDrinfeld.BruhatTits.tree R K`](def/CerednikDrinfeld_BruhatTitsTree.html#L83) whose vertices are homothety classes of full $R$-lattices in $K^2$ and whose adjacency relation is the symmetrisation of: two classes admit representatives $L$, $L'$ with `AdjacentLattice L L'`, between the standard vertex — the class of the lattice of vectors in $K^2$ both of whose coordinates are $R$-integers — and its image under the action of $g$: that distance is at most $k$.
--
--   This is the elementary half of the description of the distance function on the Bruhat–Tits tree of $\mathrm{GL}_2$ over a local field in terms of elementary divisors: an integral matrix whose determinant has valuation $k$ displaces the standard vertex by at most $k$. It is used, together with a matching lower bound, in [`CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit`](thm.html#CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit), and serves to control displacement of vertices in the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq.lean

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (CerednikDrinfeld.BruhatTits.tree R K).dist (LT.LatticeTree.stdVertex R K)
      (g • LT.LatticeTree.stdVertex R K) ≤ k := by sorry
