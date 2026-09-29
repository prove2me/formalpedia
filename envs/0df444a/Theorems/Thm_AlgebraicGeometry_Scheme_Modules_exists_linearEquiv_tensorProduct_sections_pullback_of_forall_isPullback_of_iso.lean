-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso
-- name    : AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/06b33ead-9e99-5997-bd1d-a6939821a92e
-- title:
--   Descent of tensor base change of sections along a cartesian comparison
-- statement:
--   Let $S_0$ be a commutative ring, $f_0 : A_0 \to \operatorname{Spec} S_0$ a morphism of schemes and $\mathcal L_0$ an object of `A₀.Modules`. Assume the base-change hypothesis `hbc₀`: for every commutative ring $B$, every ring homomorphism $\psi : S_0 \to B$, and every scheme $X'$ with morphisms $f' : X' \to \operatorname{Spec} B$ and $g : X' \to A_0$ forming a pullback square $g, f', f_0, \operatorname{Spec}\psi$, the map $b \otimes m \mapsto b \cdot (\text{unit of the pullback–pushforward adjunction applied to } m)$ is induced by an isomorphism $B \otimes_{S_0} \Gamma(\mathcal L_0, \top) \xrightarrow{\sim} \Gamma((\text{pullback } g)(\mathcal L_0), g^{-1}\top)$ of $B$-modules, the module structures being those obtained by restricting scalars along $S_0 \to \Gamma(A_0, \top)$ (the inverse of `ΓSpecIso` followed by $f_0^{\sharp}$ on the top open) and along $B \to \Gamma(X', g^{-1}\top)$ (likewise through $f'$), and $B$ an $S_0$-algebra via $\psi$. Let further $\psi_0 : S_0 \to S$ be a ring homomorphism, $f : A \to \operatorname{Spec} S$, $g_0 : A \to A_0$ a morphism making $g_0, f, f_0, \operatorname{Spec}\psi_0$ a pullback square, $\mathcal L$ an object of `A.Modules` and $e_0$ an isomorphism $(\text{pullback } g_0)(\mathcal L_0) \cong \mathcal L$. Then for every ring homomorphism $\varphi : S \to S'$ and every scheme $A'$ with $f' : A' \to \operatorname{Spec} S'$ and $g_A : A' \to A$ forming a pullback square over $\operatorname{Spec}\varphi$, there is an $S'$-linear equivalence $S' \otimes_S \Gamma(\mathcal L, \top) \simeq \Gamma((\text{pullback } g_A)(\mathcal L), g_A^{-1}\top)$ carrying $b \otimes m$ to $b \cdot \mathrm{pullbackLocalSection}\, g_A\, m$, with the analogous module structures through $f$, $f'$ and $\varphi$.
--
--   This is the descent step for the property “formation of global sections of $\mathcal L$ commutes with base change on the base ring”: the property, assumed for $(A_0,\mathcal L_0)$ over $S_0$ for all base changes, is transferred to any pair $(A,\mathcal L)$ obtained from it by a cartesian square together with an identification $\mathcal L \cong g_0^{*}\mathcal L_0$. It is used in the construction of the bundle of base-change properties of abelian schemes, where it supplies the base-change clause for the pulled-back family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso
    {S₀ : Type u} [CommRing S₀] {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)) (𝓛₀ : A₀.Modules)
    (hbc₀ : ∀ (B : Type u) [CommRing B] (ψ : S₀ →+* B)
      (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ A₀),
      IsPullback g f' f₀ (Spec.map (CommRingCat.ofHom ψ)) →
      letI : Module S₀ Γ(𝓛₀, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S₀)).inv ≫ f₀.appTop).hom
      letI : Module B Γ((Scheme.Modules.pullback g).obj 𝓛₀, g ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
      letI : Algebra S₀ B := ψ.toAlgebra
      ∃ e : B ⊗[S₀] Γ(𝓛₀, ⊤) ≃ₗ[B] Γ((Scheme.Modules.pullback g).obj 𝓛₀, g ⁻¹ᵁ ⊤),
        ∀ (b : B) (m : Γ(𝓛₀, ⊤)), e (b ⊗ₜ[S₀] m) = b • Scheme.Modules.pullbackLocalSection g m)
    {S : Type u} [CommRing S] (ψ₀ : S₀ →+* S) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (g₀ : A ⟶ A₀)
    (hg₀ : IsPullback g₀ f f₀ (Spec.map (CommRingCat.ofHom ψ₀)))
    (𝓛 : A.Modules) (e₀ : (Scheme.Modules.pullback g₀).obj 𝓛₀ ≅ 𝓛)
    (S' : Type u) [CommRing S'] (φ : S →+* S')
    (A' : Scheme.{u}) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A)
    (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ))) :
    letI : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
    letI : Module S' Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
    letI : Algebra S S' := φ.toAlgebra
    ∃ e : S' ⊗[S] Γ(𝓛, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤),
      ∀ (b : S') (m : Γ(𝓛, ⊤)), e (b ⊗ₜ[S] m) = b • Scheme.Modules.pullbackLocalSection gA m := by sorry
