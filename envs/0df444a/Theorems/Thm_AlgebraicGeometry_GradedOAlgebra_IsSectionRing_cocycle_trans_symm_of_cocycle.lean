-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_cocycle_trans_symm_of_cocycle
-- name    : AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/5bd8f2b9-b681-5f49-af9b-6c43c11f8747
-- title:
--   Descent cocycle for the section ring of an invertible module
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra that is faithfully flat as an $S$-module. Let $f' : X' \to \operatorname{Spec} S'$ be a morphism of schemes, $L'$ an $X'$-module that is invertible (every point has an open neighbourhood $U$ with $L'|_U$ isomorphic to the unit sheaf of modules on $U$) and satisfies `ClosedImmersionBySections L' f'`, i.e. for some $N$ there is a `ProjPresentation` of $L'$ over $f'$ by $N+1$ global sections whose associated morphism $X' \to \operatorname{Proj}$ of the homogeneous coordinate algebra is a closed immersion. Let $f'' : X'' \to \operatorname{Spec}(S' \otimes_S S')$ with $a_1, a_2 : X'' \to X'$ exhibiting $X''$ as the pullback of $f'$ along $\operatorname{Spec}$ of the left and right inclusions, and $f''' : X''' \to \operatorname{Spec}(S' \otimes_S (S' \otimes_S S'))$ with $b_{12}, b_{13}, b_{23} : X''' \to X''$ exhibiting $X'''$ as the pullback of $f''$ along $\operatorname{Spec}$ of $\mathrm{id} \otimes \iota_{\mathrm{left}}$, $\mathrm{id} \otimes \iota_{\mathrm{right}}$ and $\iota_{\mathrm{right}} : S' \otimes_S S' \to S' \otimes_S (S' \otimes_S S')$, together with the simplicial identities $b_{12} \circ a_1 = b_{13} \circ a_1$, $b_{12} \circ a_2 = b_{23} \circ a_1$, $b_{13} \circ a_2 = b_{23} \circ a_2$ (in diagrammatic order). Let $\psi : a_1^*L' \cong a_2^*L'$ be an isomorphism of modules satisfying the cocycle condition on $X'''$, stated as the equality of the displayed composite of the two comparison isomorphisms `pullbackCongr`, `pullbackComp` and $\psi$ pulled back along $b_{12}$, $b_{23}$ with the corresponding composite along $b_{13}$. Let $(R', \mathcal R', \iota')$ be a section ring of $L'$ over $f'$: $R'$ is a commutative $S'$-algebra, also an $S$-algebra with $S \to S' \to R'$ a scalar tower, graded by $S'$-submodules $\mathcal R'_n$, and $\iota'_n : \mathcal R'_n \to \Gamma(L'^{\otimes n}, \top)$ is bijective, additive, sends $s \cdot x$ to $f'^\sharp(s) \cdot \iota'_n(x)$, sends $1$ to the unit section, and is multiplicative for the isomorphisms $L'^{\otimes m} \otimes L'^{\otimes n} \cong L'^{\otimes(m+n)}$ and the tensor product of sections. Let $(R'', \mathcal R'', \iota'')$ be likewise a section ring of $a_1^*L'$ over $f''$, with $R''$ an algebra over $S' \otimes_S S'$. Let $\vartheta_1, \vartheta_2 : R' \to R''$ be $S$-algebra homomorphisms preserving degrees, such that $\iota''_n(\vartheta_1 x)$ is the canonical image of $\iota'_n(x)$ under pullback along $a_1$ (using the identity isomorphism of $a_1^*L'$) and $\iota''_n(\vartheta_2 x)$ is its image under pullback along $a_2$ followed by the $n$-th tensor power of $\psi^{-1}$, and such that $\vartheta_1(s \cdot x) = (s \otimes 1)\vartheta_1(x)$ and $\vartheta_2(s \cdot x) = (1 \otimes s)\vartheta_2(x)$ for $s \in S'$. Finally let $\beta_1 : R' \otimes_S S' \cong R''$ and $\beta_2 : S' \otimes_S R' \cong R''$ be $S$-algebra isomorphisms with $\beta_1(r \otimes t) = \vartheta_1(r)\,(1 \otimes t)$ and $\beta_2(s \otimes r) = (s \otimes 1)\,\vartheta_2(r)$. Then the transition isomorphism $\varphi := \beta_2^{-1} \circ \beta_1 : R' \otimes_S S' \cong S' \otimes_S R'$ satisfies the cocycle identity $\varphi_{02} = \varphi_{12} \circ \varphi_{01}$ over the triple tensor product, asserted as the displayed equality of two $S$-algebra homomorphisms built from $\varphi$ together with the associativity and commutativity isomorphisms of tensor products of algebras.
--
--   This is the geometric-to-algebraic transfer step in faithfully flat descent: a descent datum $\psi$ for an invertible module on the Čech nerve of $S \to S'$ produces a descent datum, in the form of a cocycle, on the graded section ring of that module. It is used by [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle), whose hypothesis on tensor-product isomorphisms is exactly the conclusion stated here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_cocycle_trans_symm_of_cocycle.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

theorem AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S'))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L') (hva : Scheme.Modules.ClosedImmersionBySections L' f')
    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L'))
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] S') R'']
    (𝓡'' : ℕ → Submodule (S' ⊗[S] S') R'') [GradedAlgebra 𝓡'']
    (ι'' : ∀ n : ℕ, 𝓡'' n → Γ(((Scheme.Modules.pullback a₁).obj L').tensorPow n, ⊤))
    (hR'' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f'' ((Scheme.Modules.pullback a₁).obj L') R'' 𝓡'' ι'')
    (ϑ₁ ϑ₂ : R' →ₐ[S] R'')
    (hϑ₁deg : ∀ n, ∀ x ∈ 𝓡' n, ϑ₁ x ∈ 𝓡'' n) (hϑ₂deg : ∀ n, ∀ x ∈ 𝓡' n, ϑ₂ x ∈ 𝓡'' n)
    (hϑ₁ : ∀ (n : ℕ) (x : 𝓡' n), ι'' n ⟨ϑ₁ x, hϑ₁deg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso a₁ L' n ≪≫
            Scheme.Modules.tensorPowMapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction a₁).unit.app (L'.tensorPow n)).app ⊤) (ι' n x)))
    (hϑ₂ : ∀ (n : ℕ) (x : 𝓡' n), ι'' n ⟨ϑ₂ x, hϑ₂deg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso a₂ L' n ≪≫ Scheme.Modules.tensorPowMapIso ψ.symm n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction a₂).unit.app (L'.tensorPow n)).app ⊤) (ι' n x)))
    (hϑ₁lin : ∀ (s : S') (x : R'), ϑ₁ (s • x) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₁ x)
    (hϑ₂lin : ∀ (s : S') (x : R'), ϑ₂ (s • x) = algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ s) * ϑ₂ x)
    (β₁ : R' ⊗[S] S' ≃ₐ[S] R'')
    (hβ₁ : ∀ (r : R') (t : S'), β₁ (r ⊗ₜ t) = ϑ₁ r * algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ t))
    (β₂ : S' ⊗[S] R' ≃ₐ[S] R'')
    (hβ₂ : ∀ (s : S') (r : R'), β₂ (s ⊗ₜ r) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₂ r) :
    let φ : R' ⊗[S] S' ≃ₐ[S] S' ⊗[S] R' := β₁.trans β₂.symm
    (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S R') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom)))) := by sorry
