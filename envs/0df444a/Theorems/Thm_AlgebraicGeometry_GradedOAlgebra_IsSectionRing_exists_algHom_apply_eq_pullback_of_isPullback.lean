-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback
-- name    : AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f67cddf3-6d1f-52e3-be44-d754c72f2baf
-- title:
--   Base-change functoriality of graded section rings
-- statement:
--   Let $S \to S'$ be a homomorphism of commutative rings, let $f : X \to \operatorname{Spec} S$ and $f' : X' \to \operatorname{Spec} S'$ be morphisms of schemes and let $c : X' \to X$ be a morphism making the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of $S \to S'$ a pullback square. Let $L$ be a module on $X$, $L'$ a module on $X'$, and $e : c^{*}L \cong L'$ an isomorphism of modules on $X'$. Let $R$ be a commutative $S$-algebra with an $\mathbb N$-grading by $S$-submodules $\mathcal R_n$ and maps $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$, where $L^{\otimes n}$ is the $n$-fold tensor power $L^{\otimes(n+1)} = L^{\otimes n} \otimes L$ with $L^{\otimes 0} = \mathbf 1$, and assume `IsSectionRing` for $(f, L, R, \mathcal R, \iota)$: each $\iota_n$ is bijective and additive, $\iota_n(s \cdot x) = \mathrm{baseScalar}(f)(s) \cdot \iota_n(x)$ for $s \in S$ (where $\mathrm{baseScalar}(f)(s) \in \Gamma(X,\top)$ is the image of $s$ under $f$ on global sections), $\iota_0(1)$ is the unit section $1 \in \Gamma(X,\top)$, and $\iota_{m+n}(xy)$ is the image of the tensor product of sections $\iota_m(x) \otimes \iota_n(y)$ under the canonical isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes(m+n)}$. Let $(R', \mathcal R'_\bullet, \iota')$ be such a datum for $(f', L')$, with $R'$ an $S'$-algebra which is also an $S$-algebra compatibly. Then there exist an $S$-algebra homomorphism $\theta : R \to R'$ and a proof that $\theta(\mathcal R_n) \subseteq \mathcal R'_n$ for all $n$, such that for every $n$ and every $x \in \mathcal R_n$ the section $\iota'_n(\theta x)$ equals the image of $\iota_n(x)$ under the unit of the adjunction $c^{*} \dashv c_{*}$ at $L^{\otimes n}$, evaluated on global sections, followed by the isomorphism $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong L'^{\otimes n}$ built from monoidality of $c^{*}$ and from $e$.
--
--   This is the functoriality of the graded ring of sections of a line bundle under a base change of the base ring: sections pull back along $c$ and, read through $e$, give a degree-preserving $S$-algebra map between the two section rings, compatible with the structure maps $\iota$, $\iota'$. It is used in the construction of the relative Picard/cocycle comparisons, notably in the results on lifting such maps to isomorphisms along the two inclusions of a tensor product of base rings and in the cocycle identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι') :
    ∃ (θ : R →ₐ[S] R') (hθdeg : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡' n),
      ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨θ x, hθdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)) := by sorry
