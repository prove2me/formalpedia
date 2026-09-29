-- Prove2me | Theorems.Thm_AlgebraicGeometry_SymmRoot_exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange
-- name    : AlgebraicGeometry.SymmRoot.exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/38257eba-7da4-5d27-b9c6-a899fb3594fc
-- title:
--   Symmetric square root over B from a two-step base change
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f\colon A\to\operatorname{Spec}S$ a morphism, $L$ a relative group law on $f$ over $S$ (functorial group structure on the $T$-points of $f$ over $\operatorname{Spec}S$), and $\mathcal L$ a module on $A$. Let $R_0$ be an $S$-algebra and $B$ simultaneously an $R_0$-algebra and an $S$-algebra, compatibly as a scalar tower. Write $A_{R_0}=A\times_{\operatorname{Spec}S}\operatorname{Spec}R_0$ and let $g_0$ be the second projection of the fibre product of $A_{R_0}\to\operatorname{Spec}R_0$ with the morphism `SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ B)))` to $\operatorname{Spec}R_0$ attached to the $R_0$-algebra $B$. Assume given a module $M_0$ on that fibre product which is invertible (locally on the source isomorphic to the unit sheaf) and satisfies `symmRootPred` for the law $L$ base changed to $R_0$ and then along $\iota$, for the pullback of $\mathcal L$ along the first projection $A_{R_0}\to A$; that is: (i) the pullback of $M_0$ along the inversion morphism $\operatorname{negMor}$ of the twice base-changed law is locally isomorphic to $M_0$ over the base, and (ii) the pullback of $\mathcal L$ to the fibre product is locally isomorphic over the base to $M_0\otimes[-1]^*M_0$. Here, for $g\colon X\to\operatorname{Spec}S'$, two modules on $X$ are locally isomorphic over the base when every point of $\operatorname{Spec}S'$ has an open neighbourhood $U$ over which their restrictions to $g^{-1}(U)$ are isomorphic. The conclusion asserts the existence of a module $M$ on $A\times_{\operatorname{Spec}S}\operatorname{Spec}B$ which is invertible, is symmetric for the base change of $L$ along $\operatorname{Spec}B\to\operatorname{Spec}S$ relative to the projection to $\operatorname{Spec}B$, and satisfies that the pullback of $\mathcal L$ along the first projection is locally isomorphic over $\operatorname{Spec}B$ to $M\otimes[-1]^*M$.
--
--   This is the transport step that converts a symmetric square root produced over the two-stage base change $S\to R_0\to B$ into one over the single base change $S\to B$, using the canonical identification $(A\times_S\operatorname{Spec}R_0)\times_{R_0}\operatorname{Spec}B\cong A\times_S\operatorname{Spec}B$ and the compatibility of the base-changed group laws. It is used in the construction of a finite faithfully flat local extension of the base over which a symmetric line bundle with $\mathcal L\simeq M\otimes[-1]^*M$ exists, where the universal element of the symmetric-root functor over the representing algebra is converted into a root on the abelian scheme itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SymmRoot_exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SymmRoot

theorem AlgebraicGeometry.SymmRoot.exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    (R₀ : Type) [CommRing R₀] [Algebra S R₀] (B : Type) [CommRing B] [Algebra S B] [Algebra R₀ B] [IsScalarTower S R₀ B]
    (M₀ : (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ B))))).Modules)
    (hM₀ : Scheme.Modules.IsInvertible M₀)
    (h₀ : symmRootPred (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))).obj 𝓛) R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ B))) M₀) :
    ∃ M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules, Scheme.Modules.IsInvertible M ∧
      IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
          (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) := by sorry
