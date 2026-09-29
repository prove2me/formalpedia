-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
-- name    : CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/556f225a-43e8-54ce-893d-27752ed2a70e
-- title:
--   Edge chart points yield Deligne data with prescribed lines
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain, with fraction field $K$ (an $\mathcal O$-algebra which is a fraction field of $\mathcal O$), let $\pi \in \mathcal O$ be irreducible, and let $q$ be a natural number equal to the cardinality of $\mathcal O/(\pi)$. Let $g \in \mathrm{GL}_2(K)$ have underlying matrix $\mathrm{diag}(\pi, 1)$, where $\pi$ is taken in $K$ via the structure map. Let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, and let $x$ be an $\mathcal O$-algebra homomorphism from the edge chart ring `chartERing 𝒪 π q`, that is from the localisation of $\mathcal O[\xi,\eta]/(\xi\eta-\pi)$ away from the element `edgeQuot.discr`, into $B$. Then there exists a Deligne datum $d$ over $B$ for $\pi$, i.e. an assignment to every full lattice $M \subseteq K^2$ of a $B$-submodule $d.\mathrm{line}\,M \subseteq B \otimes_{\mathcal O} M$ with invertible quotient, compatible with inclusions of lattices, equivariant for scalar homotheties, and satisfying the nondegeneracy condition of `DeligneDatum` at every prime of $B$, such that, writing $M_0$ for the standard lattice $\mathcal O e_0 \oplus \mathcal O e_1$ with its basis vectors `stdBasisVec`: the line at $M_0$ is the $B$-span of $x(\xi) \otimes e_0 + 1 \otimes e_1$; the line at $g \cdot M_0$ is the image of the $B$-span of $1 \otimes e_0 + x(\eta) \otimes e_1$ under the base-changed isomorphism `actBaseChange B g` induced by $g$; and $d$ satisfies `DeligneDatum.InEdgeChart`, namely the predicate `EdgeNondegAt` for $\pi$ holds at $(g \cdot M_0, M_0)$ for every prime ideal of $B$.
--
--   This is the existence half of the assertion that the standard edge chart of Drinfeld's formal upper half plane is an open subfunctor on $\pi$-nilpotent algebras: every $B$-point $(\xi_B,\eta_B)$ of the edge chart ring is realised by a Deligne datum whose kernel lines at the two ends of the standard edge are the prescribed ones. Together with the corresponding uniqueness statement it feeds the bijection between edge chart points and data lying in the edge chart, and the pullback squares used in the Mumford gluing of the standard edge charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : chartERing 𝒪 π q →ₐ[𝒪] B) :
    ∃ d : DeligneDatum (K := K) π B,
      d.line (stdFullLattice K) =
        Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
      d.line (FullLattice.act g (stdFullLattice K)) =
        (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
          (actBaseChange B g (stdFullLattice K)).toLinearMap ∧
      d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by sorry
