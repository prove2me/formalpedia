-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
-- name    : CerednikDrinfeld.FormalOmega.Omega.exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/ca01b845-0676-5481-96d9-caa04c0473c6
-- title:
--   Translated edge chart of Ω̂ is affinely representable
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring (a commutative domain) with fraction field $K_0$, let $\pi \in \mathcal O$ be irreducible, and let $q$ be the cardinality of the finite residue ring $\mathcal O/(\pi)$. Let $C$ be a Noetherian $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, let $g \in \mathrm{GL}_2(K_0)$ have matrix $\operatorname{diag}(\pi,1)$, and let $\gamma \in \mathrm{GL}_2(K_0)$ be arbitrary. Write $A_e =$ `chartERing 𝒪 π q`, the localisation of `edgeQuot 𝒪 π` $= \mathcal O[\xi,\eta]/(\,$`edgeRel 𝒪 π`$)$ away from the class `edgeQuot.discr 𝒪 π q`, and let $Y = \operatorname{Spec}(C \otimes_{\mathcal O} A_e)$, viewed over $\operatorname{Spec} C$ through $\operatorname{Spec}$ of the inclusion $C \to C \otimes_{\mathcal O} A_e$. The assertion is that there is a family of maps $\iota_S$, indexed by the $C$-algebras $S$ that are also $\mathcal O$-algebras compatibly, from the set of $C$-morphisms $\operatorname{Spec} S \to Y$ to the set of Deligne data `DeligneDatum π S` over $S$ (families of $S$-submodules of the base changes of the full $\mathcal O$-lattices in $K_0^2$, with invertible quotients, monotone, homothety-equivariant and satisfying the nondegeneracy condition at every prime of $S$), such that: $\iota$ is natural along $C$-algebra maps $\varphi : S \to S'$, the naturality being stated with respect to the action of $\varphi$ regarded as an $\mathcal O$-algebra map on `Omega K₀ π`; each $\iota_S$ is injective; and for every such $S$ a datum $d$ over $S$ satisfies `DeligneDatum.InEdgeChart π d` for the pair of lattices $(\gamma g \mathcal O^2, \gamma \mathcal O^2)$, i.e. the predicate `DeligneDatum.EdgeNondegAt` holds for this pair at every prime ideal of $S$, if and only if $d$ lies in the image of $\iota_S$.
--
--   This is the representability step in the Cerednik–Drinfeld theory of Drinfeld's formal upper half plane: on $C$-algebras in which $\pi$ is nilpotent, the subfunctor of $\hat\Omega$ cut out by the edge chart attached to the translated standard edge $(\gamma g\mathcal O^2 \subset \gamma\mathcal O^2)$ is represented by the affine $C$-scheme $\operatorname{Spec}(C \otimes_{\mathcal O} A_e)$. It feeds the construction of $\hat\Omega$ as a scheme with an open cover by these edge charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (γ : Matrix.GeneralLinearGroup (Fin 2) K₀) :
    ∃ ι : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
        (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S → (Omega K₀ π).obj S,

      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          (φ : S →ₐ[C] S') (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S),
          ι S' ((Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).map φ y) =
            (Omega K₀ π).map (φ.restrictScalars 𝒪) (ι S y)) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S], Function.Injective (ι S)) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (d : (Omega K₀ π).obj S),
          DeligneDatum.InEdgeChart π d (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
            (FullLattice.act γ (stdFullLattice K₀)) ↔ ∃ y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S, ι S y = d) := by sorry
