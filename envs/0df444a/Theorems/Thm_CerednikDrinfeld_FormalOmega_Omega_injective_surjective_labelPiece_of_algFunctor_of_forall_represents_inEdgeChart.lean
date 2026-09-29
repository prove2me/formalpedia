-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart
-- name    : CerednikDrinfeld.FormalOmega.Omega.injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/5b7aa4be-1cb4-5c6a-9918-4da99cdcae3d
-- title:
--   Label-ℓ locus maps bijectively to Ω̂
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K_0$, let $\pi$ be an irreducible element of $\mathcal{O}$, and let $q$ be the cardinality of the (finite) residue ring $\mathcal{O}/(\pi)$. Let $C$ be a Noetherian $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent, and let `PR` be an `AlgFunctor C`, that is, an assignment $S \mapsto \mathrm{PR}(S)$ on $C$-algebras together with functorial transition maps along $C$-algebra homomorphisms. The hypotheses are: (sheaf) for every $C$-algebra $A$, every finite family $f_1,\dots,f_n$ generating the unit ideal of $A$, and every choice of localisations $B_i$ away from $f_i$, sections $s_i \in \mathrm{PR}(B_i)$ whose images agree in $\mathrm{PR}(D)$ for all localisations $D$ away from $f_i f_j$ glue to a unique $s_0 \in \mathrm{PR}(A)$; a family of maps $\theta_S : \mathrm{PR}(S) \to \hat\Omega(S) =$ `(Omega K₀ π).obj S` (the set of Deligne data over $S$: for every full $\mathcal{O}$-lattice $M \subset K_0^2$ a submodule $\mathrm{line}(M) \subseteq S \otimes_{\mathcal{O}} M$ with invertible quotient, monotone in $M$, equivariant for scalar homotheties, and nondegenerate at every prime of $S$), defined for Noetherian $C$-algebras $S$ carrying a compatible $\mathcal{O}$-algebra structure and natural in $S$; a label map $\mathrm{lab}_S : \mathrm{PR}(S) \to L$ defined for Noetherian $C$-algebras $S$ all of whose idempotents are $0$ or $1$, invariant under pushforward along $C$-algebra maps with nontrivial connected target; a value $\ell \in L$; a predicate $\mathrm{Pres}_S$ on $\mathrm{PR}(S)$ with (a) $\mathrm{Pres}_S(x)$ implying $\mathrm{lab}_S(x) = \ell$ for nontrivial connected $S$ and (b) the converse for local $S$; (pts) for every algebraically closed field $k$ with compatible structure, $\theta_k$ is injective on $\{x : \mathrm{Pres}_k(x)\}$ and maps it onto $\hat\Omega(k)$; (ét) for every surjection $p : S \to S_0$ of $C$-algebras with $S$ Artinian local with algebraically closed residue field, $S_0$ nontrivial Noetherian, and $\ker p$ of square zero, every $x_0$ with $\mathrm{Pres}_{S_0}(x_0)$ and every $d \in \hat\Omega(S)$ with $\theta_{S_0}(x_0)$ the image of $d$ admit a unique lift $x \in \mathrm{PR}(S)$ with $\mathrm{Pres}_S(x)$, $\mathrm{PR}(p)(x) = x_0$ and $\theta_S(x) = d$; an element $g \in \mathrm{GL}_2(K_0)$ equal to $\mathrm{diag}(\pi, 1)$; and (rep) for every $\gamma \in \mathrm{GL}_2(K_0)$ a scheme $X$ with a locally of finite type morphism $f_X$ to $\operatorname{Spec} C$ and a natural injective family of maps $e_S$ from the $S$-points of $X$ over $C$ (morphisms $\operatorname{Spec} S \to X$ over $\operatorname{Spec} C$) into $\mathrm{PR}(S)$ whose image consists exactly of those $x$ for which $\theta_S(x)$ satisfies `DeligneDatum.InEdgeChart` for the lattice pair $(\gamma g \cdot L_{\mathrm{std}}, \gamma \cdot L_{\mathrm{std}})$, that is, is edge-nondegenerate at every prime of $S$ for these two lattices. The conclusion is that for every Noetherian $C$-algebra $S$ with compatible $\mathcal{O}$-algebra structure, writing $\mathrm{PR}_\ell(S)$ for the set of $x \in \mathrm{PR}(S)$ such that $\mathrm{lab}_k$ of the image of $x$ equals $\ell$ for every $C$-algebra homomorphism $\varphi : S \to k$ into an algebraically closed field $k$, the map $\theta_S$ is injective on $\mathrm{PR}_\ell(S)$ and every $d \in \hat\Omega(S)$ is of the form $\theta_S(x)$ with $x \in \mathrm{PR}_\ell(S)$.
--
--   This is the rigidity step in the Čerednik–Drinfeld description of the formal upper half plane: a Zariski sheaf on Noetherian $C$-algebras that is representable over each translated edge chart, matches $\hat\Omega$ on geometric points and lifts uniquely along square-zero extensions has its label-$\ell$ part in bijection with $\hat\Omega$. It is used in the construction and uniqueness of even rigidified pairs for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart

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

    {L : Type} (lab : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S],
      (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) → PR.obj S → L)
    (hlabnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [CommRing S'] [Algebra C S'] [IsNoetherianRing S']
      [Nontrivial S'] (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (hS' : ∀ e : S', IsIdempotentElem e → e = 0 ∨ e = 1)
      (g : S →ₐ[C] S') (x : PR.obj S), lab S' hS' (PR.map g x) = lab S hS x)
    (ℓ : L)
    (Pres : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S], PR.obj S → Prop)

    (hPa : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (hc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : PR.obj S), Pres S x → lab S hc x = ℓ)

    (hPb : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [IsLocalRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (hc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : PR.obj S), lab S hc x = ℓ → Pres S x)

    (hpts : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      (∀ x x' : PR.obj k, Pres k x → Pres k x' → θ k x = θ k x' → x = x') ∧
      (∀ d : (Omega K₀ π).obj k, ∃ x : PR.obj k, Pres k x ∧ θ k x = d))

    (het : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : PR.obj S₀) (d : (Omega K₀ π).obj S), Pres S₀ x₀ →
        θ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : PR.obj S, Pres S x ∧ PR.map p x = x₀ ∧ θ S x = d)

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
      (∀ x x' : PR.obj S,
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) (φ : S →ₐ[C] k),
            lab k hk (PR.map φ x) = ℓ) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) (φ : S →ₐ[C] k),
            lab k hk (PR.map φ x') = ℓ) →
          θ S x = θ S x' → x = x') ∧
      (∀ d : (Omega K₀ π).obj S, ∃ x : PR.obj S,
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) (φ : S →ₐ[C] k),
            lab k hk (PR.map φ x) = ℓ) ∧ θ S x = d) := by sorry
