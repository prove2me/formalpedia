-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/bd1691be-6615-57bc-959d-fcfa61dc83e5
-- title:
--   Finite algebra structure on the algebraised coherent module
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I \subseteq R$ an ideal with $R$ $I$-adically complete, and $f : X \to \operatorname{Spec} R$ a proper morphism of schemes. For each $n$ let $sR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ be the morphism induced by the quotient map (hypothesis `hsR`), let $tR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec}(R/I^{n+2})$ satisfy $tR_n$ followed by $sR_{n+1}$ equals $sR_n$, and let $x_n : X_n := X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1}) \to X_{n+1}$ be compatible with the first projections and with $tR_n$ on the second. Let $g_n : Y_n \to X_n$ be finite morphisms and $y_n : Y_n \to Y_{n+1}$ morphisms making each square $(y_n, g_n, g_{n+1}, x_n)$ a pullback. Let $F$ be an $\mathcal O$-module presheaf on the opens of $X$ relative to $f$ (abelian groups with compatible $R$- and $\Gamma(X,U)$-module structures and $R$-linear restrictions), which is coherent ($F(U)$ is a finite $\Gamma(X,U)$-module for every affine open $U$) and quasi-coherent (on basic opens $D(a) \subseteq U$ every section becomes $a^n$ times a restriction, and a section restricting to $0$ is killed by a power of $a$). Let $\rho_n$ be maps on affine opens, $R$-linear, $\Gamma(X,U)$-compatible and compatible with restriction, from $F(U)$ to $\Gamma(Y_n, h_n^{-1}U)$ where $h_n$ is $g_n$ followed by the projection $X_n \to X$, such that each $\rho_n$ is surjective on affine opens, has kernel $I^{n+1} \cdot F(U)$, and $\rho_n$ equals $\rho_{n+1}$ followed by pullback along $y_n$. Then there exist a functor $A$ from the opposite of the affine Zariski site of $X$ to commutative rings, a natural transformation $\alpha$ from $U \mapsto \Gamma(X,U)$ to $A$ all of whose naturality squares are pushouts of rings, and additive bijections $e_U : A(U) \to F(U)$ for all affine opens $U$, such that every $\alpha_U$ is a finite ring homomorphism, $e_U(\alpha_U(a) \cdot x) = a \cdot e_U(x)$, the $e_U$ commute with the restrictions of $A$ and of $F$, and for every $n$ and $U$ the composite $\rho_n \circ e_U : A(U) \to \Gamma(Y_n, h_n^{-1}U)$ is a ring homomorphism.
--
--   This is the algebra-theoretic refinement of Grothendieck's existence theorem in the form needed here: the coherent module $F$ algebraising the adic system of finite algebras $\Gamma(Y_n, h_n^{-1}(-))$ is shown to carry the structure of a quasi-coherent $\mathcal O_X$-algebra, finite over $\mathcal O_X$ and presented as a coequifibered functor on the affine Zariski site, for which the comparison maps $\rho_n$ become ring homomorphisms. It feeds the statements producing a finite $X$-scheme that algebraises the system $(Y_n, y_n)$, namely [`AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete) and its variant for a closed immersion projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
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
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))
    (F : OModulePresheaf f) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (ρ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (hρc : ∀ (n : ℕ) (U : X.affineOpens) (x : F.obj U.1),
      (ρ n).app U x =
        ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom
          ((ρ (n + 1)).app U x)) :
    ∃ (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
      (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A) (_ : α.Coequifibered)
      (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1),
      (∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) ∧
      (∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
        e U ((α.app (op U)).hom a * x) = a • e U x) ∧
      (∀ (U V : X.AffineZariskiSite) (i : V ⟶ U) (x : A.obj (op U)),
        e V ((A.map i.op).hom x) = F.res (Scheme.AffineZariskiSite.toOpens_mono i.le) (e U x)) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        ∃ r : A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1),
          ∀ x : A.obj (op U), r x = (ρ n).app ⟨U.1, U.2⟩ (e U x)) := by sorry
