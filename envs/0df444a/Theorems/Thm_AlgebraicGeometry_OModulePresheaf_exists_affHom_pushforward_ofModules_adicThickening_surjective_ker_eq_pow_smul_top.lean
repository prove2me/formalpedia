-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/a5bf6994-1737-5169-8805-38b052cb6424
-- title:
--   Pushforwards of invertible modules along adic thickenings
-- statement:
--   Let $R$ be a commutative ring, $I\subseteq R$ an ideal, $X$ a scheme and $f\colon X\to\operatorname{Spec} R$ a morphism; for $n\in\mathbb N$ let $X_n=\operatorname{adicThickening} f\,I\,n$ be the fibre product of $f$ with $\operatorname{Spec}(R/I^{n+1})\to\operatorname{Spec} R$, with $\iota_n\colon X_n\to X$ and the transition map $\tau_n\colon X_n\to X_{n+1}$ over $X$. Assume given, for each $n$, a module $L_n$ on $X_n$ which is invertible in the sense that every point of $X_n$ lies in an open $U$ with $U.\iota^*L_n$ isomorphic to the unit sheaf of modules on $U$, together with, for each $n$, an isomorphism $\tau_n^*L_{n+1}\cong L_n$. Write $F_n$ for the $\mathcal O$-module presheaf on $X$ over $f$ given by $U\mapsto\Gamma(L_n,\iota_n^{-1}U)$, with $\Gamma(X,U)$ acting through $\iota_n$ and $R$ through $\iota_n$ followed by $f$. The conclusion asserts: each $F_n$ is coherent, i.e. $F_n(U)$ is a finite $\Gamma(X,U)$-module for every affine open $U$ of $X$; each $F_n$ is quasi-coherent, i.e. for every affine open $U$ and $g\in\Gamma(X,U)$ every section over the basic open of $g$ becomes, after multiplication by some power of $g$, a restriction from $U$, and every section over $U$ restricting to $0$ there is killed by a power of $g$; and there is a family of maps $\varphi_n\colon F_{n+1}\to F_n$, each given on affine opens $U$ by $R$-linear maps compatible with the $\Gamma(X,U)$-actions and with restriction along inclusions of affine opens, such that every $\varphi_n$ on $U$ is surjective with kernel exactly $I^{n+1}\cdot F_{n+1}(U)$.
--
--   This is the algebraic input to Grothendieck's existence theorem in formal geometry in the shape used here: a compatible system of invertible modules on the $I$-adic thickenings of $X$ gives an adic system of coherent, quasi-coherent module data on $X$. It is used in the construction of invertible modules on a scheme from data on its thickenings, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_forall_thickening_of_forall_exists_isCoherent`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_forall_thickening_of_forall_exists_isCoherent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (L : ∀ n : ℕ, (adicThickening f I n).Modules)
    (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
    (hcompat : ∀ n, Nonempty
      ((Scheme.Modules.pullback (adicThickeningTransition f I n)).obj (L (n + 1)) ≅ L n)) :
    (∀ n : ℕ, (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))).IsCoherent) ∧
    (∀ n : ℕ, (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))).IsQuasicoherent) ∧
    ∃ φ : ∀ n : ℕ, OModulePresheaf.AffHom
        (OModulePresheaf.pushforward f (adicThickeningι f I (n + 1))
          (OModulePresheaf.ofModules (adicThickeningι f I (n + 1) ≫ f) (L (n + 1))))
        (OModulePresheaf.pushforward f (adicThickeningι f I n)
          (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))),
      (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((φ n).app U)) ∧
      (∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((φ n).app U) =
        I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.pushforward f (adicThickeningι f I (n + 1))
          (OModulePresheaf.ofModules (adicThickeningι f I (n + 1) ≫ f) (L (n + 1)))).obj U.1))) := by sorry
