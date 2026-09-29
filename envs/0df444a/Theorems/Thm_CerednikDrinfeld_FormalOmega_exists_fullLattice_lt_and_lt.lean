-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_fullLattice_lt_and_lt
-- name    : CerednikDrinfeld.FormalOmega.exists_fullLattice_lt_and_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/43bb4b41-326c-5d46-bda6-b5cc62e7bca0
-- title:
--   Every full lattice has a neighbour between π M and M
-- statement:
--   Let $\mathcal{O}$ be a commutative domain which is a discrete valuation ring, and let $K$ be a field equipped with an $\mathcal{O}$-algebra structure making it the fraction field of $\mathcal{O}$. Let $\pi \in \mathcal{O}$ be irreducible, and let $M$ be a full lattice in $K^2$, that is, an $\mathcal{O}$-submodule $M \subseteq (\mathrm{Fin}\ 2 \to K)$ which is finitely generated and whose $K$-span is all of $K^2$ (the type `FullLattice` bundles the submodule with this pair of conditions). The assertion is that there exists a further full lattice $M'$ such that, in the lattice of $\mathcal{O}$-submodules of $K^2$, $$\mathrm{latticeMap}(\mathrm{scalarGL}(u))\,M \;<\; M' \;<\; M,$$ both inequalities being strict. Here $u = \mathrm{unitOfNeZero}$ applied to the nonvanishing of $\pi$ is the unit $\mathrm{algebraMap}_{\mathcal{O},K}(\pi) \in K^\times$; $\mathrm{scalarGL}(u)$ is the element $u \cdot 1$ of $\mathrm{GL}_2(K)$, with inverse $u^{-1} \cdot 1$; and $\mathrm{latticeMap}(g)L$ is the image of $L$ under the $\mathcal{O}$-linear map $v \mapsto g \cdot v$ on $K^2$. Thus $\pi M \subsetneq M' \subsetneq M$, with $M'$ again a full lattice.
--
--   This is the existence of a neighbouring vertex in the Bruhat–Tits tree of $\mathrm{GL}_2(K)$: the homothety classes of full lattices strictly between $M$ and $\pi M$ are the vertices adjacent to the class of $M$, so the statement says that every vertex has at least one neighbour, i.e. that the pair $(\pi M, M)$ is not forced to degenerate. It is used in the Čerednik–Drinfeld part of the development, in the construction of edge charts for the Deligne datum, where a degenerate pair $M' \in \{M, \pi M\}$ must be replaced by a genuine edge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_fullLattice_lt_and_lt.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_fullLattice_lt_and_lt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (M : FullLattice 𝒪 K) :
    ∃ M' : FullLattice 𝒪 K, latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 ∧ M'.1 < M.1 := by sorry
