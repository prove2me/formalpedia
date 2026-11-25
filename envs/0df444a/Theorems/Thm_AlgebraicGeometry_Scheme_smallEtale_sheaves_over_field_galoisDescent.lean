-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_smallEtale_sheaves_over_field_galoisDescent
-- name    : AlgebraicGeometry.Scheme.smallEtale_sheaves_over_field_galoisDescent
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-25T10:52:36.273149+00:00
-- url     : https://prove2.me/theorems/63c9b384-cad9-5d8c-9439-ecaff8a44a1e
-- title:
--   Galois descent for étale sheaves over a field: étale sheaves of Λ-modules on Spec κ are the discrete Gal(κ^sep/κ)-modules, via the stalk at a geometric point
-- statement:
--   Let $X$ be a scheme and $x_0 \in X$ a point such that the canonical morphism $\operatorname{Spec}\kappa(x_0) \to X$ is an isomorphism, so that $X$ is the spectrum of the field $\kappa = \kappa(x_0)$. Let $\Omega = \kappa^{\mathrm{sep}}$ be the separable closure of $\kappa$, let $\Gamma = \mathrm{Gal}(\Omega/\kappa)$ with its Krull topology, and let $\bar x\colon \operatorname{Spec}\Omega \to \operatorname{Spec}\kappa \cong X$ be the corresponding geometric point. Let $\Lambda$ be a commutative ring. For a sheaf $F$ of $\Lambda$-modules on the small étale site of $X$, let $F_{\bar x}$ be its stalk at $\bar x$, the colimit of $F(U)$ over the étale $X$-schemes $U$ together with a lift $a\colon \operatorname{Spec}\Omega \to U$ of $\bar x$. An element $\sigma \in \Gamma$ acts on $F_{\bar x}$ by sending the germ of $s \in F(U)$ at the lift $a$ to the germ of $s$ at the lift $a \circ \operatorname{Spec}\sigma$. Then:
--
--   1. every $v \in F_{\bar x}$ has an open stabilizer in $\Gamma$, i.e. $F_{\bar x}$ is a discrete $\Gamma$-module;
--   2. for every morphism $\varphi\colon F \to G$ of étale sheaves, the stalk map $\varphi_{\bar x}\colon F_{\bar x} \to G_{\bar x}$ is $\Gamma$-equivariant;
--   3. every $\Gamma$-equivariant $\Lambda$-linear map $f\colon F_{\bar x} \to G_{\bar x}$ is $\varphi_{\bar x}$ for a unique morphism of sheaves $\varphi\colon F \to G$;
--   4. every discrete $\Gamma$-module over $\Lambda$ (a $\Lambda$-linear representation $\rho$ of $\Gamma$ on a module $M$ in which every element has an open stabilizer) is $\Gamma$-equivariantly isomorphic to $F_{\bar x}$ for some étale sheaf $F$ of $\Lambda$-modules on $X$.
--
--   Together, $F \mapsto F_{\bar x}$ is an equivalence between the category of étale sheaves of $\Lambda$-modules on $\operatorname{Spec}\kappa$ and the category of discrete $\Lambda$-linear $\Gamma$-modules.
--
--   This is the dictionary between étale sheaves over a field and Galois modules (Grothendieck's Galois descent): it is what identifies the étale cohomology of $\operatorname{Spec}\kappa$ with the Galois cohomology of $\kappa$, and it describes the stalks of a sheaf at the geometric points of any scheme as Galois modules. It is proved here for arbitrary étale sheaves (no finiteness or local constancy) and an arbitrary coefficient ring $\Lambda$. Part 4 is the essential surjectivity: the sheaf is $U \mapsto \{\Gamma\text{-equivariant maps from the set of lifts of } \bar x \text{ to } U \text{ into } M\}$, whose stalk is $M$ because every element of $M$ is fixed by the subgroup fixing some finite subextension $E \subseteq \Omega$, and $\operatorname{Spec} E \to X$ is étale.
--
--   **Formalization Note**: The small étale site is `X.smallEtaleTopology`, and étale sheaves of $\Lambda$-modules are `Sheaf X.smallEtaleTopology (ModuleCat Λ)`. The hypothesis that $X$ is the spectrum of a field is `[IsIso (X.fromSpecResidueField x0)]`; $\kappa$ is `X.residueField x0`, $\Omega$ is `SeparableClosure κ` and $\Gamma$ is `Ω ≃ₐ[κ] Ω` with Mathlib's Krull topology; a discrete module is one in which every element is fixed by some open subgroup `H`. The geometric point is the variable `pt` with defining equation `hpt`. Mathlib's `Scheme.pointSmallEtale pt` is the corresponding point of the small étale site, whose fibre at an étale `U` is the set of lifts `Over.mk pt ⟶ U`, and the stalk $F_{\bar x}$ is `((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat Λ)).obj F`. The variable `g σ` (defining hypothesis `hg`) is $\operatorname{Spec}\sigma$ as an endomorphism of `Over.mk pt`; precomposition with it, $a \mapsto a \circ \operatorname{Spec}\sigma$, is an endomorphism of the point, and `GrothendieckTopology.Point.Hom.sheafFiber` turns it into the action `rep F σ` of $\sigma$ on the stalk (variable with defining equation `hrep`). Each of `pt`, `g` and `rep` is uniquely determined by its defining hypothesis. All types live in one universe `u`.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §1 (sheaves on the étale site of a field and discrete Galois modules); A. Grothendieck, M. Artin, J.-L. Verdier, Théorie des topos et cohomologie étale des schémas (SGA 4), Exposé VIII

import Mathlib

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.smallEtale_sheaves_over_field_galoisDescent
    {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)]
    (Λ : Type u) [CommRing Λ]
    (pt : Spec (CommRingCat.of (SeparableClosure (X.residueField x0))) ⟶ X)
    (hpt : pt = Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField x0) (SeparableClosure (X.residueField x0)))) ≫ X.fromSpecResidueField x0)
    (g : (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0] SeparableClosure (X.residueField x0)) →
      (Over.mk pt ⟶ Over.mk pt))
    (hg : ∀ σ, (g σ).left = Spec.map (CommRingCat.ofHom
      (σ : SeparableClosure (X.residueField x0) →+* SeparableClosure (X.residueField x0))))
    (rep : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ),
      (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0] SeparableClosure (X.residueField x0)) →
        (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F →ₗ[Λ]
          ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F))
    (hrep : ∀ F σ, rep F σ =
      ((GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u} Λ)
        (⟨Functor.whiskerLeft (Scheme.Etale.forget X)
          (coyoneda.map (g σ).op)⟩ :
            Scheme.pointSmallEtale pt ⟶ Scheme.pointSmallEtale pt)).app F).hom) :
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
      (v : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F),
      ∃ H : Subgroup (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0)),
        IsOpen (H : Set (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0))) ∧ ∀ σ ∈ H, rep F σ v = v) ∧
    (∀ (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (φ : F ⟶ G) σ,
      (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).map φ).hom ∘ₗ rep F σ =
        rep G σ ∘ₗ (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).map φ).hom) ∧
    (∀ (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
      (f : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F →ₗ[Λ]
        ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj G),
      (∀ σ, f ∘ₗ rep F σ = rep G σ ∘ₗ f) →
        ∃! φ : F ⟶ G, (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).map φ).hom = f) ∧
    ∀ (M : Type u) [AddCommGroup M] [Module Λ M]
      (ρ : Representation Λ (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
        SeparableClosure (X.residueField x0)) M),
      (∀ m : M, ∃ H : Subgroup (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0)),
        IsOpen (H : Set (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0))) ∧ ∀ σ ∈ H, ρ σ m = m) →
      ∃ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
        (e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F ≃ₗ[Λ] M),
        ∀ σ v, e (rep F σ v) = ρ σ (e v) := by
  sorry
