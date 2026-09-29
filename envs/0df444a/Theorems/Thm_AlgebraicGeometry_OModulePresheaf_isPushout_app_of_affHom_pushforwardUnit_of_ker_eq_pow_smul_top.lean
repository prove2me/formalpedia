-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/dea83fe9-0f70-5a44-ab7c-8a54e3af899b
-- title:
--   Levelwise pushout squares for an algebraised adic system
-- statement:
--   Fix a commutative ring $R$, an ideal $I \subseteq R$, a scheme $X$ and a morphism $f : X \to \operatorname{Spec} R$. For each $n$ let $sR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ be given, assumed equal to $\operatorname{Spec}$ of the quotient map, write $\iota_n$ for the first projection of the pullback of $f$ along $sR_n$, and let $g_n : Y_n \to X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ be morphisms. Let $F$ be an `OModulePresheaf` for $f$: an assignment $U \mapsto F(U)$ on the opens of $X$ carrying compatible $R$- and $\Gamma(X,U)$-module structures (the $R$-algebra structure on $\Gamma(X,U)$ coming from $f$) together with $R$-linear, semilinear restriction maps. Let $\psi_n$ be an `AffHom` from $F$ to the pushforward along $g_n \circ \iota_n$ of the unit presheaf, i.e. for every affine open $U$ an $R$-linear map $F(U) \to \Gamma(Y_n, (g_n \circ \iota_n)^{-1}U)$ that is $\Gamma(X,U)$-semilinear and commutes with restrictions; assume each $\psi_n$ on affine opens is surjective with kernel $I^{n+1} \cdot F(U)$. Let $A$ be a functor from the opposite affine Zariski site of $X$ to commutative rings, $\alpha$ a natural transformation from $U \mapsto \Gamma(X,U)$ to $A$, and $e_U : A(U) \xrightarrow{\sim} F(U)$ additive isomorphisms satisfying $e_U(\alpha_U(a)\,x) = a \cdot e_U(x)$; let $r_{n,U} : A(U) \to \Gamma(Y_n,(g_n \circ \iota_n)^{-1}U)$ be ring homomorphisms with $r_{n,U}(x) = \psi_n(e_U(x))$ on affine opens. Then for every $n$ and every affine open $U$ of $X$ the square formed by $\alpha_U$, the map $\Gamma(X,U) \to \Gamma(X \times_R \operatorname{Spec}(R/I^{n+1}), \iota_n^{-1}U)$ induced by $\iota_n$, $r_{n,U}$ and the map induced by $g_n$ on $\iota_n^{-1}U$ is a pushout square in the category of commutative rings.
--
--   This is the levelwise comparison step for an adic system of algebras presented by an $\mathcal{O}_X$-module datum: on each affine open, the ring of sections of $Y_n$ is the base change of $A(U)$ along $\Gamma(X,U) \to \Gamma(X,U)/I^{n+1}\Gamma(X,U)$. It is used by [`AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered`](thm.html#AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered), where such squares are glued into a morphism over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
    (R : Type u) [CommRing R] (I : Ideal R)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n))
    (F : OModulePresheaf f)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    (hψk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
    (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A)
    (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1)
    (hlin : ∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
      e U ((α.app (op U)).hom a * x) = a • e U x)
    (r : ∀ (n : ℕ) (U : X.AffineZariskiSite), A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1))
    (hr : ∀ (n : ℕ) (U : X.AffineZariskiSite) (x : A.obj (op U)), r n U x = (ψ n).app ⟨U.1, U.2⟩ (e U x))
    (n : ℕ) (U : X.AffineZariskiSite) :
    IsPushout (α.app (op U)) ((pullback.fst f (sR n)).app U.1) (CommRingCat.ofHom (r n U))
      ((g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)) := by sorry
