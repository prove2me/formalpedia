-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL
-- name    : CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/4cc9667a-42ac-5040-be5c-4054d6a1de0a
-- title:
--   Homothetic lattices have determinant indices of equal parity
-- statement:
--   Let $\mathcal{O}$ be a commutative domain which is a discrete valuation ring, and let $K$ be a field equipped with an $\mathcal{O}$-algebra structure making it the fraction field of $\mathcal{O}$. Let $\pi \in \mathcal{O}$ be irreducible, let $N$ be an $\mathcal{O}$-submodule of $K^{2}$ (the functions $\mathrm{Fin}\,2 \to K$), let $c \in K^{\times}$ and let $e, e' \in \mathbb{Z}$. Here the predicate `HasDetIndex π N e` asserts that there is $g \in \mathrm{GL}_2(K)$ with $g \cdot \mathrm{stdLattice}\,\mathcal{O}\,K = N$, where `stdLattice` is the submodule of vectors all of whose coordinates lie in the image of $\mathcal{O}$ and $g$ acts by $v \mapsto g \mathbin{*_v} v$ (this is `latticeMap`), and such that $\det g = u \cdot \pi^{e}$ in $K$ for some unit $u \in \mathcal{O}^{\times}$ (images under the structure map understood). Assume `HasDetIndex π N e` holds, and also `HasDetIndex π (latticeMap (scalarGL c) N) e'`, where `scalarGL c` is the scalar matrix $c \cdot 1$ in $\mathrm{GL}_2(K)$, so that the second lattice is $cN$. The conclusion is that $e - e'$ is even.
--
--   This is the bipartition of the vertices of the Bruhat–Tits tree of $\mathrm{SL}_2(K)$ by the parity of the valuation of the determinant: homothetic lattices lie in the same class. It underlies the determinant normalisation distinguishing the two lattices of a Drinfeld quadruple, and is used in the characterisations of the quadruple condition `DrinfeldDatum.IsQuadrupleOf` and its variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (N : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (e e' : ℤ)
    (h : HasDetIndex π N e) (h' : HasDetIndex π (latticeMap (scalarGL c) N) e') : Even (e - e') := by sorry
