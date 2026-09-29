-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/2b28a66e-fa86-51b7-a18e-7a4847eb636c
-- title:
--   Deligne datum in the standard edge chart: existence of chart point
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring with fraction field $K$, let $\pi \in \mathcal O$ be irreducible, let $q$ be a natural number equal to `Nat.card` of the residue ring $\mathcal O/(\pi)$, assumed finite, and let $g \in \mathrm{GL}_2(K)$ have matrix $\mathrm{diag}(\pi, 1)$ (with $\pi$ taken in $K$ via the structure map). Let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, and let $d$ be a Deligne datum over $B$ for $\pi$: an assignment to every full $\mathcal O$-lattice $M \subset K^2$ of a $B$-submodule $d.\mathrm{line}\,M \subseteq B \otimes_{\mathcal O} M$ with invertible quotient, compatible with lattice inclusions, equivariant for scalar homotheties, and nondegenerate at every prime of $B$ in the sense of the `nondeg` clause. Assume further that $d$ satisfies the predicate `DeligneDatum.InEdgeChart` for the pair $(g \cdot M_0, M_0)$, where $M_0$ is the standard full lattice $\mathcal O^2$; by definition this says that for every prime ideal $\mathfrak p$ of $B$ the predicate `DeligneDatum.EdgeNondegAt` holds at $\mathfrak p$ for this pair. Then there is an $\mathcal O$-algebra homomorphism $x$ from the edge chart ring `chartERing 𝒪 π q` — the localisation of $\mathrm{MvPoly}(\mathrm{Fin}\,2, \mathcal O)$ modulo the single relation `edgeRel 𝒪 π` away from the image of `edgeDiscr 𝒪 q` — to $B$, such that $d.\mathrm{line}\,M_0$ is the $B$-span of $x(\xi) \otimes e_0 + 1 \otimes e_1$, where $\xi$ and $\eta$ denote the distinguished elements `chartERing.ξ 𝒪 π q` and `chartERing.η 𝒪 π q` and $e_0, e_1$ the standard basis vectors of $M_0$, and $d.\mathrm{line}(g \cdot M_0)$ is the image of the $B$-span of $1 \otimes e_0 + x(\eta) \otimes e_1$ under the base-changed isomorphism $B \otimes_{\mathcal O} M_0 \xrightarrow{\sim} B \otimes_{\mathcal O} (g \cdot M_0)$ induced by $g$.
--
--   This is the chart-level representability step for Drinfeld's formal upper half plane: a Deligne datum over $B$ whose lines are nondegenerate along the standard edge joining the vertices of $M_0$ and $\mathrm{diag}(\pi,1)M_0$ is induced by an $\mathcal O$-point of the corresponding edge chart ring, with the two lines written in the explicit coordinates $\xi, \eta$. It is used to obtain the unique and functorial such chart point, to produce coverings by edge charts pulling back to the standard edge, and in the Mumford glueing of the chart data into a formal scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K)) :
    ∃ x : chartERing 𝒪 π q →ₐ[𝒪] B,
      d.line (stdFullLattice K) =
        Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
      d.line (FullLattice.act g (stdFullLattice K)) =
        (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
          (actBaseChange B g (stdFullLattice K)).toLinearMap := by sorry
