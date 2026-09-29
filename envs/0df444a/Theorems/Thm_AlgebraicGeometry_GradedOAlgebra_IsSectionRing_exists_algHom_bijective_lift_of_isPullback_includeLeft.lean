-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeLeft
-- name    : AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeLeft
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/38685e0e-741d-5255-a8c8-543f65e3b1f2
-- title:
--   Section rings compare along the first coface of a flat base change
-- statement:
--   Let $S$ be a commutative ring and $S'$ a flat $S$-algebra, and write $S'' = S'\otimes_S S'$. Let $f' : X' \to \operatorname{Spec} S'$ be a quasi-compact separated morphism of schemes, $f'' : X'' \to \operatorname{Spec} S''$ a morphism, and $a : X'' \to X'$ a morphism making the square with $f''$, $f'$ and $\operatorname{Spec}$ of the ring map underlying $\mathrm{includeLeft} : S' \to S''$, $s \mapsto s \otimes 1$, a pullback square. Let $L'$ be a module on $X'$ that is invertible in the sense that every point of $X'$ has an open neighbourhood $U$ for which the pullback of $L'$ along $U \hookrightarrow X'$ is isomorphic to the unit sheaf of modules on $U$, let $L''$ be a module on $X''$, and let $e : a^{*}L' \cong L''$. Let $R'$ be a commutative ring that is an $S'$-algebra and an $S$-algebra compatibly, equipped with a graded algebra structure $\mathcal R'_\bullet$ by $S'$-submodules indexed by $\mathbb N$, and maps $\iota'_n : \mathcal R'_n \to \Gamma(L'^{\otimes n}, \top)$, where $L'^{\otimes 0}$ is the monoidal unit and $L'^{\otimes (n+1)} = L'^{\otimes n} \otimes L'$; assume `IsSectionRing` for $f'$, $L'$, i.e. each $\iota'_n$ is bijective and additive, $\iota'_n(s\cdot x) = \mathrm{baseScalar}(f')(s)\cdot\iota'_n(x)$ for $s \in S'$ (where $\mathrm{baseScalar}(f')(s)$ is the image of $s$ in $\Gamma(X', \top)$ under $f'$), $\iota'_0(1)$ is the unit section $1$, and $\iota'_{m+n}(xy)$ is the tensor product of sections $\iota'_m(x)$ and $\iota'_n(y)$ transported by the canonical isomorphism $L'^{\otimes m}\otimes L'^{\otimes n} \cong L'^{\otimes(m+n)}$. Assume likewise that $R''$, with grading $\mathcal R''_\bullet$ by $S''$-submodules and maps $\iota''_n$, is a section ring for $f''$ and $L''$. Then there is an $S$-algebra homomorphism $\vartheta : R' \to R''$ with $\vartheta(\mathcal R'_n) \subseteq \mathcal R''_n$ for all $n$ such that: (i) for $x \in \mathcal R'_n$, $\iota''_n(\vartheta x)$ is obtained from $\iota'_n(x)$ by applying the unit of the pullback–pushforward adjunction for $a$ at $L'^{\otimes n}$ on global sections and then the isomorphism $a^{*}(L'^{\otimes n}) \cong (a^{*}L')^{\otimes n} \cong L''^{\otimes n}$ induced by $e$; (ii) $\vartheta(s \cdot x) = \mathrm{algebraMap}(s \otimes 1)\,\vartheta(x)$ for $s \in S'$, $x \in R'$; (iii) each $\mathcal R''_n$ is contained in the $S''$-span of $\vartheta(\mathcal R'_n)$; and (iv) the $S$-algebra map $R' \otimes_S S' \to R''$ lifting $\vartheta$ on the left and $t \mapsto \mathrm{algebraMap}(1 \otimes t)$ on the right is bijective.
--
--   This packages, for the first of the two cofaces $S' \to S' \otimes_S S'$, the functoriality of the graded section ring of an invertible module under base change together with its compatibility with flat base change, in the form needed for descent: the section ring upstairs is the base change of the one downstairs, degreewise and globally. It is used in the proof of [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle), the descent step for line bundles along a faithfully flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeLeft.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

theorem AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeLeft
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X' X'' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) [QuasiCompact f'] [IsSeparated f']
    (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a : X'' ⟶ X')
    (ha : IsPullback a f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
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
      (∀ (s : S') (x : R'), ϑ (s • x) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ x) ∧
      (∀ n, 𝓡'' n ≤ Submodule.span (S' ⊗[S] S') (ϑ '' (𝓡' n : Set R'))) ∧
      Function.Bijective
        (Algebra.TensorProduct.lift ϑ
          ((IsScalarTower.toAlgHom S (S' ⊗[S] S') R'').comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S'))
          (fun _ _ => Commute.all _ _) : R' ⊗[S] S' →ₐ[S] R'') := by sorry
