-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
-- name    : CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/d4cd6425-66f6-5446-a4f6-1a0358e2ec55
-- title:
--   Edge transitivity of GL₂(K) on full lattices
-- statement:
--   Let $\mathcal O$ be a domain which is a discrete valuation ring, with $K$ an $\mathcal O$-algebra that is a field and a fraction field of $\mathcal O$, and let $\pi \in \mathcal O$ be irreducible. Let $g \in \mathrm{GL}_2(K)$ be an element whose underlying matrix is $\mathrm{diagonal}(\pi, 1)$, the image of $\pi$ in $K$ occupying the first diagonal entry. Let $M'$ and $M$ be full lattices in $K^2 = (\mathrm{Fin}\,2 \to K)$, i.e. $\mathcal O$-submodules satisfying `IsFullLattice`, and assume that the image of $M$ under the scalar matrix $\pi \cdot 1$ (the unit of $K$ attached to $\pi$, nonzero because $\pi$ is irreducible, acting through `scalarGL`) is strictly contained in $M'$, and that $M'$ is strictly contained in $M$. Then there exists $h \in \mathrm{GL}_2(K)$ such that the image of the standard lattice $\{v : \text{each } v_i \text{ lies in } \mathcal O\}$ under $v \mapsto h \cdot v$ equals $M$, and the image of $g \cdot (\text{standard lattice})$ under $v \mapsto h\cdot v$ equals $M'$; both equalities are equalities of full lattices, i.e. of the underlying submodules of $K^2$.
--
--   This is the transitivity of $\mathrm{GL}_2(K)$ on the ordered edges of the Bruhat–Tits tree of $\mathrm{SL}_2(K)$, stated for exact lattices rather than homothety classes: any pair $\pi M < M' < M$ can be carried simultaneously onto the standard pair $\mathrm{diag}(\pi,1)\mathcal O^2 \subset \mathcal O^2$. It is used to move the nondegenerate pair of lattices of a Deligne datum into the standard edge chart, and is cited by the edge-chart lemmas for Deligne data such as [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing); the proof appeals to the corresponding vertex-transitivity statement [`LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice`](thm.html#LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (M' M : FullLattice 𝒪 K)
    (h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1) (h₂ : M'.1 < M.1) :
    ∃ h : Matrix.GeneralLinearGroup (Fin 2) K,
      FullLattice.act h (stdFullLattice K) = M ∧ FullLattice.act h (FullLattice.act g (stdFullLattice K)) = M' := by sorry
