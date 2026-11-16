-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_lisse_smallEtale_equiv_unramified_genericFibre
-- name    : AlgebraicGeometry.Scheme.lisse_smallEtale_equiv_unramified_genericFibre
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:16:02.68986+00:00
-- url     : https://prove2.me/theorems/17b95200-6712-49dc-8b98-d5f17b0621e8
-- title:
--   Lisse étale sheaves on $\mathrm{Spec}\,A$ are classified by the Galois action on the generic geometric stalk
-- statement:
--   Let $A$ be a noetherian integrally closed domain with fraction field $K$, let $X = \mathrm{Spec}\,A$, and let $\Lambda$ be a commutative ring. Let $\eta$ be the generic point of $X$, $\kappa = \kappa(\eta)$ its residue field (canonically isomorphic to $K$), $\Omega = \kappa^{\mathrm{sep}}$ a separable closure, $\Gamma = \mathrm{Gal}(\Omega/\kappa)$, and $\bar\eta : \mathrm{Spec}\,\Omega \to X$ the generic geometric point. For a sheaf $F$ of $\Lambda$-modules on the small étale site $X_{\mathrm{et}}$ write $F_{\bar\eta}$ for its stalk at $\bar\eta$, and for an étale $U \to X$, a lift $a : \mathrm{Spec}\,\Omega \to U$ of $\bar\eta$ and $s \in F(U)$ write $s_a \in F_{\bar\eta}$ for the germ of $s$ at $a$.
--
--   A sheaf $F$ is *lisse* (locally constant constructible) if every point $x \in X$ is in the image of some étale $U \to X$ over which $F$ becomes isomorphic to a constant sheaf $M_X$ with $M$ a finitely generated $\Lambda$-module. A subgroup $H \le \Gamma$ is *unramified over $A$* if there are a finite Galois extension $L/K$ inside $\overline K$ that is unramified over $A$ (for every prime $\mathfrak P$ of the integral closure $A_L$ of $A$ in $L$, the only $\sigma \in \mathrm{Gal}(L/K)$ with $\sigma(b) \equiv b \pmod{\mathfrak P}$ for all $b \in A_L$ is $\sigma = 1$) and an embedding $\iota : L \to \Omega$ extending $A \to \kappa \to \Omega$ such that $H$ contains every $\sigma \in \Gamma$ that fixes $\iota(L)$ pointwise. Equivalently, $H$ contains the preimage of an open subgroup of $\pi_1(X, \bar\eta) = \mathrm{Gal}(K^{\mathrm{ur}}/K)$, where $K^{\mathrm{ur}}$ is the maximal extension of $K$ unramified over $A$.
--
--   **Theorem.** There is a unique family of representations $\rho_F : \Gamma \to \mathrm{Aut}_\Lambda(F_{\bar\eta})$, one for each étale sheaf $F$, such that for every étale $U \to X$, all lifts $a, b$ of $\bar\eta$ to $U$ with $b = a \circ \mathrm{Spec}\,\sigma$, and all $s \in F(U)$,
--
--   $$\rho_F(\sigma)(s_a) = s_b .$$
--
--   For these actions:
--
--   1. for every étale sheaf $F$ and every lisse $G$, each $\Gamma$-equivariant $\Lambda$-linear map $F_{\bar\eta} \to G_{\bar\eta}$ is the stalk of a morphism of sheaves $F \to G$;
--   2. two morphisms between lisse sheaves that agree on stalks at $\bar\eta$ are equal;
--   3. lisse sheaves whose generic stalks are $\Gamma$-equivariantly isomorphic are isomorphic;
--   4. for lisse $F$, the stalk $F_{\bar\eta}$ is a finitely generated $\Lambda$-module and $\ker \rho_F$ is unramified over $A$;
--   5. every finitely generated $\Lambda$-module $V$ with a representation of $\Gamma$ whose kernel is unramified over $A$ is $\Gamma$-equivariantly isomorphic to $F_{\bar\eta}$ for some lisse $F$.
--
--   In other words, $F \mapsto F_{\bar\eta}$ is an equivalence of categories
--
--   $$\{\text{lisse étale sheaves of } \Lambda\text{-modules on } \mathrm{Spec}\,A\} \;\simeq\; \{\text{finitely generated } \Lambda\text{-modules with a continuous action of } \pi_1(\mathrm{Spec}\,A, \bar\eta)\}.$$
--
--   This is the classical dictionary between locally constant constructible sheaves and representations of the étale fundamental group (Grothendieck's Galois theory of SGA 1 applied to the étale covers trivialising a lisse sheaf), stated at the generic point of a normal noetherian affine scheme, where $\pi_1$ is a quotient of the absolute Galois group of the function field. It is the step that turns lisse $\ell$-adic sheaves on a curve over a finite field into Galois representations of its function field unramified outside the missing points, and conversely.
--
--   **Formalization Note**: $X$ is `Spec (.of A)` and étale sheaves are `Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ)` on Mathlib's small étale site; constant sheaves are `constantSheaf`. The generic point is a variable `η` with `IsGenericPoint η ⊤`; $\kappa$ is `(Spec (.of A)).residueField η`, $\Omega$ is `SeparableClosure κ` and $\Gamma$ is `Ω ≃ₐ[κ] Ω`. The geometric point is a variable `pt` with defining equation `hpt` (the map induced by `κ → Ω` followed by `fromSpecResidueField η`). The stalk is `(Scheme.pointSmallEtale pt).sheafFiber.obj F`, and the germ of `z : F(U)` at a lift `a : Over.mk pt ⟶ (Scheme.Etale.forget _).obj U` is `(Scheme.pointSmallEtale pt).toPresheafFiber U a F.obj z`. The predicates *lisse* and *unramified* are variables `IsLisse`, `Unr` fixed by the defining equivalences `hIsLisse`, `hUnr`. In `hIsLisse` the restriction of `F` to `U` is the presheaf `(Over.forget U).op ⋙ F.obj` on the slice of the étale site over `U` (equivalent to the small étale site of `U`), compared with the same restriction of `M_X`; finite generation is `Module.Finite Λ M`. In `hUnr`, $L$ is `L : IntermediateField K (AlgebraicClosure K)` with `FiniteDimensional K L` and `IsGalois K L`, $A_L$ is `integralClosure A L`, the congruence is written elementwise as `∃ c ∈ P, (c : L) = σ b - b`, and the compatibility of `ι : L →+* Ω` with $A \to \kappa \to \Omega$ is `Spec.map (CommRingCat.ofHom (ι.comp (algebraMap A L))) = pt`. The family $\rho$ is a dependent function `∀ F, Representation Λ Γ (stalk F)`; uniqueness and the germ rule are stated together as `∀ ρ', ρ' = ρ ↔ (germ rule for ρ')`, where $b = a \circ \mathrm{Spec}\,\sigma$ is `b.left = Spec.map (CommRingCat.ofHom σ) ≫ a.left`. Equivariance is `∀ σ v, f (ρ F σ v) = ρ G σ (f v)`, item 1 is `(sheafFiber.map φ).hom = f`, item 2 compares `sheafFiber.map φ` and `sheafFiber.map ψ`, and the kernel in items 4 and 5 is `(ρ F).ker`. The hypotheses are satisfiable (for example $A = \mathbb{Z}$, $K = \mathbb{Q}$, $\Lambda = \mathbb{Z}/2$; every domain has a generic point, and `IsLisse`, `Unr`, `pt` are determined by their defining equations), and the conclusion is not vacuous: the constant sheaf $\Lambda_X$ is lisse.
-- source:
--   A. Grothendieck, Revêtements étales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Exposé V §§7-8; M. Artin, A. Grothendieck, J.-L. Verdier, Théorie des topos et cohomologie étale des schémas (SGA 4), Lecture Notes in Math. 305, Springer (1973), Exposé IX §2; J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter I §5; E. Freitag, R. Kiehl, Étale Cohomology and the Weil Conjecture, Ergebnisse 13, Springer (1988), Chapter I

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.lisse_smallEtale_equiv_unramified_genericFibre
    (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (Λ : Type) [CommRing Λ]
    (η : Spec (.of A)) (hη : IsGenericPoint η ⊤)
    (pt : Spec (.of (SeparableClosure ((Spec (.of A)).residueField η))) ⟶ Spec (.of A))
    (hpt : pt = Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of A)).residueField η)
        (SeparableClosure ((Spec (.of A)).residueField η)))) ≫ (Spec (.of A)).fromSpecResidueField η)
    (IsLisse : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ) → Prop)
    (hIsLisse : ∀ F, IsLisse F ↔ ∀ x : Spec (.of A),
      ∃ (U : (Spec (.of A)).Etale) (v : U.left), U.hom v = x ∧
        ∃ M : ModuleCat Λ, Module.Finite Λ M ∧
          Nonempty ((Over.forget U).op ⋙ F.obj ≅
            (Over.forget U).op ⋙ ((constantSheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ)).obj M).obj))
    (Unr : Subgroup (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
      SeparableClosure ((Spec (.of A)).residueField η)) → Prop)
    (hUnr : ∀ H, Unr H ↔ ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ IsGalois K L ∧
      (∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
        (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1) ∧
      ∃ ι : L →+* SeparableClosure ((Spec (.of A)).residueField η),
        Spec.map (CommRingCat.ofHom (ι.comp (algebraMap A L))) = pt ∧
        ∀ σ, (∀ x : L, σ (ι x) = ι x) → σ ∈ H) :
    ∃ ρ : ∀ F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ),
        Representation Λ (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F),
      (∀ ρ', ρ' = ρ ↔ ∀ F (σ : SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) (U : (Spec (.of A)).Etale) (a b : Over.mk pt ⟶ (Scheme.Etale.forget _).obj U),
        b.left = Spec.map (CommRingCat.ofHom (σ : _ →+* _)) ≫ a.left →
        ∀ z, ρ' F σ ((Scheme.pointSmallEtale pt).toPresheafFiber U a F.obj z) =
          (Scheme.pointSmallEtale pt).toPresheafFiber U b F.obj z) ∧
      (∀ F G, IsLisse G →
        ∀ f : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F →ₗ[Λ] ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj G,
        (∀ σ v, f (ρ F σ v) = ρ G σ (f v)) →
        ∃ φ : F ⟶ G, (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map φ).hom = f) ∧
      (∀ F G, IsLisse F → IsLisse G → ∀ φ ψ : F ⟶ G,
        ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map φ = ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).map ψ → φ = ψ) ∧
      (∀ F G, IsLisse F → IsLisse G →
        ∀ e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F ≃ₗ[Λ] ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj G,
        (∀ σ v, e (ρ F σ v) = ρ G σ (e v)) → Nonempty (F ≅ G)) ∧
      (∀ F, IsLisse F →
        Module.Finite Λ (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F) ∧ Unr (ρ F).ker) ∧
      (∀ (V : Type) [AddCommGroup V] [Module Λ V], Module.Finite Λ V →
        ∀ ρV : Representation Λ (SeparableClosure ((Spec (.of A)).residueField η) ≃ₐ[(Spec (.of A)).residueField η]
          SeparableClosure ((Spec (.of A)).residueField η)) V, Unr ρV.ker →
        ∃ F, IsLisse F ∧ ∃ e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F ≃ₗ[Λ] V,
          ∀ σ w, e (ρ F σ w) = ρV σ (e w)) := by
  sorry
