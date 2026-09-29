-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/2c6bd27b-e21d-5a75-b764-d8cd5cae8c60
-- title:
--   Zariski-local reduction of Deligne data to the standard edge chart
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain, $K$ a field which is a fraction field of $\mathcal O$, $\pi \in \mathcal O$ an irreducible element, and $q$ a natural number equal to the cardinality of the residue ring $\mathcal O/(\pi)$, assumed finite. Let $g \in \mathrm{GL}_2(K)$ have underlying matrix $\mathrm{diag}(\pi, 1)$, and let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent. Let $d$ be a Deligne datum for $\pi$ over $B$, i.e. an assignment $M \mapsto d.\mathrm{line}(M)$ of a $B$-submodule of the base change $B \otimes_{\mathcal O} M$ to each full $\mathcal O$-lattice $M \subset K^2$, with invertible quotients, monotone under inclusions of lattices, equivariant for homothety actions, and satisfying the nondegeneracy condition `nondeg` at every prime of $B$. The assertion is that there is a finite subset $s \subset B$ generating the unit ideal such that for every $r \in s$ there exist $h \in \mathrm{GL}_2(K)$ and an $\mathcal O$-algebra homomorphism $x$ from the edge-chart ring `chartERing 𝒪 π q` (the localisation of the edge quotient ring at its discriminant element) to the localisation $B[1/r]$ for which the datum $d_r$, obtained by base change of $d$ along $B \to B[1/r]$ and then pullback along $h$ (so $d_r.\mathrm{line}(M)$ is the preimage of the $B[1/r]$-line at $h\cdot M$ under the base-changed action of $h$), satisfies three conditions: first, `InEdgeChart` for the pair $(g \cdot \mathcal O^2, \mathcal O^2)$, i.e. the predicate `EdgeNondegAt` for $\pi$ holds at every prime ideal of $B[1/r]$ with respect to the lattices $g\cdot \mathcal O^2$ and $\mathcal O^2$; second, $d_r.\mathrm{line}$ at the standard lattice $\mathcal O^2$ is the $B[1/r]$-span of the single element $x(\xi) \otimes e_0 + 1 \otimes e_1$; and third, $d_r.\mathrm{line}$ at $g \cdot \mathcal O^2$ is the image, under the base-changed action of $g$, of the span of $1 \otimes e_0 + x(\eta) \otimes e_1$, where $e_0, e_1$ are the standard basis vectors of $\mathcal O^2$ and $\xi, \eta$ the distinguished elements of the edge-chart ring.
--
--   This is the target-side local statement that the edge charts of Drinfeld's formal upper half plane cover it and that, $\mathrm{GL}_2(K)$ acting transitively on the edges of the Bruhat–Tits tree, every point with values in an $\mathcal O$-algebra in which $\pi$ is nilpotent becomes, Zariski-locally and after a translation, a point of the standard edge chart described explicitly by $\xi, \eta$. It is used in the comparison of the functor of Deligne data with the formal scheme $\widehat\Omega$ and in the Zariski-local construction of quadruples on the special formal side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (d : DeligneDatum (K := K) π B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧ ∀ r ∈ s,
      ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K) (x : chartERing 𝒪 π q →ₐ[𝒪] Localization.Away r),
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).InEdgeChart π
          (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) ∧
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).line (stdFullLattice K) =
          Submodule.span (Localization.Away r)
            {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : Localization.Away r) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).line (FullLattice.act g (stdFullLattice K)) =
          (Submodule.span (Localization.Away r)
            {(1 : Localization.Away r) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
            (actBaseChange (Localization.Away r) g (stdFullLattice K)).toLinearMap := by sorry
