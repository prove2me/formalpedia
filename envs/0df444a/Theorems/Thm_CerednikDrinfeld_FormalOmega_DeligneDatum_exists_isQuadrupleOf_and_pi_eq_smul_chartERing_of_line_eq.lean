-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/9233e4f4-5e21-5782-9649-0a1432d58913
-- title:
--   Explicit Drinfeld quadruple over the standard edge chart
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K$, let $\pi \in \mathcal{O}$ be irreducible, and let $q$ be the (finite) cardinality of the residue ring $\mathcal{O}/(\pi)$. Let $g \in \mathrm{GL}_2(K)$ have matrix $\mathrm{diag}(\pi,1)$, and let $B$ be a commutative $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent. Let $d$ be a Deligne datum for $\pi$ over $B$, that is, an assignment to each full $\mathcal{O}$-lattice $M \subset K^2$ of a $B$-submodule $d.\mathrm{line}\,M \subseteq B \otimes_{\mathcal{O}} M$ with invertible quotient, compatible with lattice inclusions and with the homothety action of $K^\times$, and satisfying the nondegeneracy condition of `DeligneDatum` at every prime of $B$; assume further that $d$ lies in the edge chart of the pair $(g\cdot\mathcal{O}^2, \mathcal{O}^2)$, i.e. `DeligneDatum.EdgeNondegAt` holds for $d$, $\pi$ and this pair at every prime ideal of $B$. Let $x \colon$ `chartERing` $\mathcal{O}\,\pi\,q \to B$ be an $\mathcal{O}$-algebra map, where `chartERing` is the localisation of the edge quotient ring away from its discriminant `edgeQuot.discr`, with distinguished elements $\xi, \eta$. Assume the two lines are in chart normal form: $d.\mathrm{line}(\mathcal{O}^2)$ is the $B$-span of $x(\xi) \otimes e_0 + 1 \otimes e_1$, and $d.\mathrm{line}(g\cdot\mathcal{O}^2)$ is the image, under the base change `actBaseChange` of the isomorphism $\mathcal{O}^2 \cong g\cdot\mathcal{O}^2$, of the $B$-span of $1 \otimes e_0 + x(\eta) \otimes e_1$, where $e_0, e_1$ are the standard basis vectors of the standard full lattice. Then there exists a Drinfeld datum $Q$ for $\pi$ over $B$ (lattice families $N_0 \subseteq N_1$ over $\mathrm{Spec}\,B$, invertible $B$-modules $T_0, T_1$, maps $\Pi_0, \Pi_1$ with both composites equal to multiplication by $\pi$, and local trivialisations $u_0, u_1$) which is a quadruple of $d$ in the sense of `IsQuadrupleOf` — at every prime $x$ of $B$ the pair $(Q.L_0 x, Q.L_1 x)$ is edge-nondegenerate for $d$ at $x$ and the kernels of $u_0 x$, $u_1 x$ are the lines of the datum obtained from $d$ by base change to the local ring at $x$ — together with elements $e_0 \in T_0$ and $e_1 \in T_1$ such that every element of $T_0$ (respectively $T_1$) is $b \cdot e_0$ (respectively $b \cdot e_1$) for a unique $b \in B$, and $$\Pi_0 e_0 = -x(\eta)\, e_1, \qquad \Pi_1 e_1 = -x(\xi)\, e_0.$$
--
--   This is the local comparison, on the standard edge chart of the Bruhat–Tits tree, between Deligne's description of the formal upper half-plane and Drinfeld's moduli data: it produces the quadruple attached to a chart point and computes the two structure maps $\Pi_0, \Pi_1$ in the chart coordinates $\xi, \eta$ (whose product is $\pi$). It is used in [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_unit_eq_mul_chartERing_eta_of_line_eq`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_unit_eq_mul_chartERing_eta_of_line_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K))
    (x : chartERing 𝒪 π q →ₐ[𝒪] B)
    (hx0 : d.line (stdFullLattice K) =
      Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (hx1 : d.line (FullLattice.act g (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g (stdFullLattice K)).toLinearMap)
 :
    ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d ∧
      ∃ (e₀ : Q.T₀) (e₁ : Q.T₁), (∀ t : Q.T₀, ∃! b : B, t = b • e₀) ∧ (∀ t : Q.T₁, ∃! b : B, t = b • e₁) ∧
        Q.Pi₀ e₀ = (-(x (chartERing.η 𝒪 π q))) • e₁ ∧ Q.Pi₁ e₁ = (-(x (chartERing.ξ 𝒪 π q))) • e₀ := by sorry
