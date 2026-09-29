-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeRight
-- name    : AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/b5537e5a-12a9-5b20-a993-1f0a5b9bca40
-- title:
--   Section rings along the second coface of a flat base change
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is flat as an $S$-module, and write $S'' = S' \otimes_S S'$. Let $f' : X' \to \operatorname{Spec} S'$ be a quasi-compact separated morphism of schemes, let $f'' : X'' \to \operatorname{Spec} S''$ be a morphism, and let $a : X'' \to X'$ be such that the square formed by $a$, $f''$, $f'$ and $\operatorname{Spec}$ of the second coface $S' \to S''$, $s \mapsto 1 \otimes s$, is cartesian. Let $L'$ be a module on $X'$ which is invertible in the sense that every point has an open neighbourhood $U$ over which the restriction of $L'$ is isomorphic to the unit sheaf of $U$, let $L''$ be a module on $X''$, and let $e : a^{*}L' \cong L''$. Let $R'$ be a commutative ring which is an $S'$-algebra and an $S$-algebra compatibly, graded by submodules $\mathcal R'_n \subseteq R'$ over $S'$, and let $\iota'_n : \mathcal R'_n \to \Gamma(L'^{\otimes n}, \top)$ (tensor powers formed recursively, with $L'^{\otimes 0}$ the unit) exhibit $(R', \mathcal R'_\bullet, \iota')$ as a section ring for $f'$ and $L'$: each $\iota'_n$ is bijective and additive, $\iota'_n(s \cdot x) = \beta(s)\,\iota'_n(x)$ for the global function $\beta(s)$ obtained from $s \in S'$ along $f'$, $\iota'_0(1)$ is the unit section $1$, and $\iota'_{m+n}(xy)$ is the image of the tensor product of sections $\iota'_m(x)$ and $\iota'_n(y)$ under the canonical isomorphism $L'^{\otimes m} \otimes L'^{\otimes n} \cong L'^{\otimes m+n}$. Let $(R'', \mathcal R''_\bullet, \iota'')$ be likewise a section ring for $f''$ and $L''$, over $S''$. Then there is an $S$-algebra homomorphism $\vartheta : R' \to R''$ such that $\vartheta(\mathcal R'_n) \subseteq \mathcal R''_n$ for all $n$; for $x \in \mathcal R'_n$, $\iota''_n(\vartheta x)$ is the image of $\iota'_n(x)$ under the unit of the pullback–pushforward adjunction at $L'^{\otimes n}$ on global sections followed by the isomorphism $a^{*}(L'^{\otimes n}) \cong (a^{*}L')^{\otimes n} \cong L''^{\otimes n}$ induced by $e$; $\vartheta(s \cdot x) = \operatorname{algebraMap}(1 \otimes s)\,\vartheta(x)$ for $s \in S'$, $x \in R'$; each $\mathcal R''_n$ lies in the $S''$-span of $\vartheta(\mathcal R'_n)$; and the $S$-algebra map $S' \otimes_S R' \to R''$ with components $S' \to S'' \to R''$ through the first coface and $\vartheta$ is bijective.
--
--   This packages, for the second coface of a flat base change, the functoriality of the section ring of an invertible module together with its compatibility with flat base change, in the form needed to compare the two pullbacks of a section ring to $\operatorname{Spec}(S' \otimes_S S')$. It is used in the proof of [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle), where a line bundle with a cocycle datum is descended along a faithfully flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeRight.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

theorem AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeRight
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X' X'' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) [QuasiCompact f'] [IsSeparated f']
    (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a : X'' ⟶ X')
    (ha : IsPullback a f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L') (L'' : X''.Modules) (e : (Scheme.Modules.pullback a).obj L' ≅ L'')
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] S') R'']
    (𝓡'' : ℕ → Submodule (S' ⊗[S] S') R'') [GradedAlgebra 𝓡'']
    (ι'' : ∀ n : ℕ, 𝓡'' n → Γ(L''.tensorPow n, ⊤)) (hR'' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f'' L'' R'' 𝓡'' ι'') :
    ∃ (ϑ : R' →ₐ[S] R'') (hϑdeg : ∀ n, ∀ x ∈ 𝓡' n, ϑ x ∈ 𝓡'' n),
      (∀ (n : ℕ) (x : 𝓡' n), ι'' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso a L' n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app (L'.tensorPow n)).app ⊤) (ι' n x))) ∧
      (∀ (s : S') (x : R'), ϑ (s • x) = algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ s) * ϑ x) ∧
      (∀ n, 𝓡'' n ≤ Submodule.span (S' ⊗[S] S') (ϑ '' (𝓡' n : Set R'))) ∧
      Function.Bijective
        (Algebra.TensorProduct.lift
          ((IsScalarTower.toAlgHom S (S' ⊗[S] S') R'').comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) ϑ
          (fun _ _ => Commute.all _ _) : S' ⊗[S] R' →ₐ[S] R'') := by sorry
