-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_mul_eq_and_map_eq_of_isBaseChange_of_inEdgeChart
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_mul_eq_and_map_eq_of_isBaseChange_of_inEdgeChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/d9467801-79c6-591e-b3d2-5103aca03671
-- title:
--   Lifting a quadruple's (α,β) with αβ=π
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K$, let $\pi\in\mathcal O$ be irreducible, let $\mathcal O/(\pi)$ be finite of cardinality $q$, and let $g\in\mathrm{GL}_2(K)$ have matrix $\mathrm{diag}(\pi,1)$. Let $B,B'$ be commutative $\mathcal O$-algebras, $\varphi\colon B'\to B$ a surjective $\mathcal O$-algebra map whose kernel is a nilpotent ideal, and suppose the image of $\pi$ in $B'$ is nilpotent. Let $d$ be a Deligne datum over $B$ for $\pi$ (a line, i.e. a $B$-submodule with invertible quotient, in $B\otimes_{\mathcal O}M$ for every full lattice $M\subset K^2$, monotone in $M$, equivariant for scalar homotheties, and nondegenerate at every prime of $B$), satisfying the predicate `DeligneDatum.EdgeNondegAt` at every prime of $B$ for the pair $(g\cdot L_{\mathrm{std}},L_{\mathrm{std}})$, where $L_{\mathrm{std}}=\mathcal O^2$. Let $x\colon$ `chartERing 𝒪 π q` $\to B$ be an $\mathcal O$-algebra map such that the line of $d$ at $L_{\mathrm{std}}$ is spanned by $x(\xi)\otimes e_0+1\otimes e_1$ and the line at $g\cdot L_{\mathrm{std}}$ is the image under `actBaseChange` of the span of $1\otimes e_0+x(\eta)\otimes e_1$, where $e_0,e_1$ is the standard basis. Let $Q$ be a Drinfeld datum over $B$ for $\pi$ (a pair of lattice families over $\mathrm{Spec}\,B$ together with invertible modules $T_0,T_1$, maps $\Pi_0,\Pi_1$ with both composites multiplication by $\pi$, and trivialisations $u_0,u_1$ on stalks) which is a quadruple of $d$: at each prime $\mathfrak p$ the datum $d$ localised at $\mathfrak p$ is edge-nondegenerate for $(L_0,L_1)$ at $\mathfrak p$ and the kernels of $u_0,u_1$ are the lines of the localised datum at $L_0,L_1$. Let $e_0\in T_0$, $e_1\in T_1$ be elements such that every element of $T_0$ (resp. $T_1$) is uniquely a $B$-multiple of $e_0$ (resp. $e_1$), and let $\alpha,\beta\in B$ satisfy $\Pi_0e_0=\alpha e_1$ and $\Pi_1e_1=\beta e_0$. Finally let $d'$ be a Deligne datum over $B'$ for $\pi$ whose base change along $\varphi$ is $d$, i.e. the line of $d$ at each full lattice $M$ is `lineBaseChange` of the line of $d'$ at $M$. Then there are $\alpha',\beta'\in B'$ with $\varphi(\alpha')=\alpha$, $\varphi(\beta')=\beta$ and $\alpha'\beta'$ equal to the image of $\pi$ in $B'$.
--
--   This is the chart-local infinitesimal lifting step on the $\widehat\Omega$ side of the Čerednik–Drinfeld uniformisation: given a lift of a point of the formal upper half plane along a surjection with nilpotent kernel, the pair $(\alpha,\beta)$ describing $\Pi_0,\Pi_1$ on a trivialised Drinfeld quadruple lifts, together with the relation $\alpha'\beta'=\pi$. It feeds the covering statement [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange), where the chart hypotheses are provided locally on $\mathrm{Spec}\,B$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_mul_eq_and_map_eq_of_isBaseChange_of_inEdgeChart.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_mul_eq_and_map_eq_of_isBaseChange_of_inEdgeChart
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    (φ : B' →ₐ[𝒪] B) (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker (φ : B' →+* B)))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K))
    (x : chartERing 𝒪 π q →ₐ[𝒪] B)
    (hx0 : d.line (stdFullLattice K) =
      Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (hx1 : d.line (FullLattice.act g (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g (stdFullLattice K)).toLinearMap)
    (Q : DrinfeldDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d)
    (e₀ : Q.T₀) (e₁ : Q.T₁)
    (he₀ : ∀ t : Q.T₀, ∃! b : B, t = b • e₀) (he₁ : ∀ t : Q.T₁, ∃! b : B, t = b • e₁)
    (α β : B) (hα : Q.Pi₀ e₀ = α • e₁) (hβ : Q.Pi₁ e₁ = β • e₀)
    (d' : DeligneDatum (K := K) π B') (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) φ d' d) :
    ∃ α' β' : B', φ α' = α ∧ φ β' = β ∧ α' * β' = algebraMap 𝒪 B' π := by sorry
