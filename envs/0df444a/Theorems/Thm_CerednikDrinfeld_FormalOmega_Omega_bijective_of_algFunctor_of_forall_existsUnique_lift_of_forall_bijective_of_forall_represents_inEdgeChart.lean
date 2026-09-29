-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
-- name    : CerednikDrinfeld.FormalOmega.Omega.bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/2cc25239-26f2-53f6-8b6d-4be41c383787
-- title:
--   Formal rigidity for Ω̂: chart-wise representable functors
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K_0$, let $\pi \in \mathcal O$ be irreducible, and suppose the residue ring $\mathcal O/(\pi)$ is finite of cardinality $q$. Let $C$ be a Noetherian $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, and let `PR` be an `AlgFunctor` over $C$, that is, an assignment $B \mapsto \mathrm{PR}(B)$ of a set to each commutative $C$-algebra together with functorial transition maps along $C$-algebra homomorphisms. Four hypotheses are imposed on `PR` and on a family of maps $\theta_S : \mathrm{PR}(S) \to \hat\Omega(S)$, where $\hat\Omega(S) =$ `(Omega K₀ π).obj S` is the set of Deligne data over $S$ (a family of $S$-submodules $\mathrm{line}(M) \subseteq S \otimes_{\mathcal O} M$, indexed by the full lattices $M \subset K_0^2$, with invertible quotient, monotone in $M$, equivariant for scalar homotheties, and nondegenerate at every prime of $S$), defined for all Noetherian $C$-algebras $S$ carrying an $\mathcal O$-algebra structure compatible with $C$. These are: (sheaf) for every $C$-algebra $A$, every finite family $f : \mathrm{Fin}\,n \to A$ generating the unit ideal, and localisations $B_i$ of $A$ away from $f_i$, any family of sections $s_i \in \mathrm{PR}(B_i)$ agreeing on all localisations away from $f_i f_j$ (for every such $D$ and all $A$-algebra maps $B_i \to D$, $B_j \to D$) glues to a unique $s_0 \in \mathrm{PR}(A)$; (naturality) $\theta$ commutes with the transition maps of `PR` and of $\hat\Omega$ along $C$-algebra homomorphisms; (lifting) for every Artinian local $C$-algebra $S$ as above with algebraically closed residue field, every nontrivial $C$-algebra $S_0$ as above, and every surjective $C$-algebra map $p : S \to S_0$ whose kernel satisfies $st = 0$ for all $s,t \in \ker p$, and all $x_0 \in \mathrm{PR}(S_0)$, $d \in \hat\Omega(S)$ with $\theta_{S_0}(x_0)$ the image of $d$, there is a unique $x \in \mathrm{PR}(S)$ lying over $x_0$ with $\theta_S(x) = d$; (points) $\theta_k$ is bijective for every algebraically closed field $k$ that is a $C$- and $\mathcal O$-algebra compatibly. Finally, with $g \in \mathrm{GL}_2(K_0)$ the diagonal matrix $\mathrm{diag}(\pi,1)$, it is assumed that for each $\gamma \in \mathrm{GL}_2(K_0)$ there exist a scheme $X$, a morphism $f_X : X \to \operatorname{Spec} C$ locally of finite type, and maps $e_S$ from the set of $S$-points of $f_X$ over $\operatorname{Spec} C$ (pairs consisting of a morphism $\operatorname{Spec} S \to X$ whose composite with $f_X$ is the structure morphism) to $\mathrm{PR}(S)$, which are compatible with base change along $C$-algebra maps, injective for each $S$, and whose image in $\mathrm{PR}(S)$ consists exactly of those $x$ for which the Deligne datum $\theta_S(x)$ satisfies, at every prime ideal of $S$, the edge-nondegeneracy condition `DeligneDatum.EdgeNondegAt` for the ordered pair of full lattices $(\gamma g \Lambda_{\mathrm{std}}, \gamma \Lambda_{\mathrm{std}})$, $\Lambda_{\mathrm{std}}$ being the standard lattice. The conclusion is that $\theta_S$ is bijective for every Noetherian $C$-algebra $S$ with compatible $\mathcal O$-algebra structure.
--
--   This is an abstract-functor rigidity criterion for Drinfeld's formal upper half plane: a Zariski sheaf on $C$-algebras equipped with a natural, formally smooth-by-lifting transformation to the functor of Deligne data, bijective on algebraically closed points and with representable edge-chart preimages, is isomorphic to $\hat\Omega$ on all Noetherian $C$-algebras. It is used in the identification of functors of fake elliptic curves with rigidifications, and in the corresponding labelled-piece statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (PR : AlgFunctor C)
    (hsheaf : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i)

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      PR.obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (φ : S →ₐ[C] S') (x : PR.obj S),
      θ S' (PR.map φ x) = (Omega K₀ π).map (φ.restrictScalars 𝒪) (θ S x))

    (het : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : PR.obj S₀) (d : (Omega K₀ π).obj S),
        θ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : PR.obj S, PR.map p x = x₀ ∧ θ S x = d)

    (hpts : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      Function.Bijective (θ k))

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (hrep : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) K₀,
      ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) (_ : LocallyOfFiniteType fX)
        (e : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
          (Scheme.nilpPoints fX).obj S → PR.obj S),

        (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
            (y : (Scheme.nilpPoints fX).obj S)
            (y' : (Scheme.nilpPoints fX).obj S'),
            y'.1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ y.1 → e S' y' = PR.map φ (e S y)) ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            (y y' : (Scheme.nilpPoints fX).obj S), e S y = e S y' → y = y') ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (x : PR.obj S),
            (∃ y : (Scheme.nilpPoints fX).obj S, e S y = x) ↔
              DeligneDatum.InEdgeChart π (θ S x) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
                (FullLattice.act γ (stdFullLattice K₀)))) :
    ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      Function.Bijective (θ S) := by sorry
