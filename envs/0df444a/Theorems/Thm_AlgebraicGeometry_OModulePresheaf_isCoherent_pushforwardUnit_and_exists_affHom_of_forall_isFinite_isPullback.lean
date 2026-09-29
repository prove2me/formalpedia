-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
-- name    : AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/05ecf772-22f0-559f-8999-20c87f6870f6
-- title:
--   Coherence of pushforwards along a compatible system of finite morphisms
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I \subseteq R$ an ideal with $R$ $I$-adically complete, and $f : X \to \operatorname{Spec} R$ a proper morphism of schemes. Assume given, for each $n$, the morphism $s_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ induced by the quotient map, morphisms $t_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec}(R/I^{n+2})$ with $t_n$ followed by $s_{n+1}$ equal to $s_n$, and morphisms $x_n : X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1}) \to X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+2})$ commuting with the first projections and intertwining the second projections with $t_n$. Assume further given schemes $Y_n$, finite morphisms $g_n : Y_n \to X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$, and morphisms $y_n : Y_n \to Y_{n+1}$ such that each square $(y_n, g_n, g_{n+1}, x_n)$ is a pullback. Write $\mathcal B_n$ for the $\mathcal O$-module presheaf on $X$ over $\operatorname{Spec} R$ obtained by pushing forward the unit presheaf along $g_n$ followed by the first projection, so $\mathcal B_n(U) = \Gamma(Y_n, (\mathrm{pr}_1 \circ g_n)^{-1}U)$ with $\Gamma(X,U)$ acting through pullback of functions. Then: (i) each $\mathcal B_n$ is coherent, i.e. $\mathcal B_n(U)$ is a finite $\Gamma(X,U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and every $a \in \Gamma(X,U)$ each section over the basic open $D(a)$ becomes, after multiplication by some power of $a$, the restriction of a section over $U$, and a section over $U$ restricting to $0$ on $D(a)$ is killed by a power of $a$; (ii) $I^{n+1}$ annihilates $\mathcal B_n(U)$ for every open $U \subseteq X$ and every $n$; and (iii) there are maps $\tau_n$ of $\mathcal O$-module presheaves on affine opens from $\mathcal B_{n+1}$ to $\mathcal B_n$ ($R$-linear on each affine open, semilinear for the $\Gamma(X,U)$-action and compatible with restriction between affine opens) such that on each affine open $U$ the map $\tau_n$ is pullback of functions along $y_n$, is surjective, and has kernel $I^{n+1}\,\mathcal B_{n+1}(U)$.
--
--   This is the standard coherence and base-change package for the direct images $\mathcal B_n = (\mathrm{pr}_1 \circ g_n)_* \mathcal O_{Y_n}$ attached to a compatible cartesian system of finite schemes over the truncations $X \times_R \operatorname{Spec}(R/I^{n+1})$; it produces the adic system of coherent algebras that Grothendieck's existence theorem takes as input. It is used in the algebraisation step over an $I$-adically complete base, feeding the construction of the limit module and of the finite morphism over $X$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)) :
    (∀ n : ℕ, (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsCoherent ∧
      (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsQuasicoherent) ∧
    (∀ (n : ℕ) (U : X.Opens),
      I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).obj U)) = ⊥) ∧
    ∃ τ : ∀ n : ℕ, OModulePresheaf.AffHom
        (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1))))
        (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))),
      (∀ (n : ℕ) (U : X.affineOpens)
        (x : (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1),
        (τ n).app U x =
          ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1)
            ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
            (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom x) ∧
      (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((τ n).app U)) ∧
      (∀ (n : ℕ) (U : X.affineOpens),
        LinearMap.ker ((τ n).app U) =
          I ^ (n + 1) • (⊤ : Submodule R
            ((OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1))) := by sorry
