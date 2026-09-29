-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered
-- name    : AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/23086b58-f515-5db8-89a1-14f6486ae802
-- title:
--   Levelwise maps to the relative spectrum and pushout squares
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I \subseteq R$ an ideal with $R$ $I$-adically complete, $X$ a scheme and $f : X \to \operatorname{Spec} R$ proper. Let $sR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ be the morphisms induced by the quotient maps, and $tR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec}(R/I^{n+2})$ transition morphisms with $tR_n$ followed by $sR_{n+1}$ equal to $sR_n$; let $x_n$ be morphisms of the pullbacks $X_n := X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ commuting with both projections (the second up to $tR_n$). Let $g_n : Y_n \to X_n$ be finite morphisms and $y_n : Y_n \to Y_{n+1}$ morphisms such that each square $(y_n, g_n, g_{n+1}, x_n)$ is a pullback. Let $F$ be an $\mathcal{O}$-module presheaf over $f$: an assignment of an $R$-module and a $\Gamma(X,U)$-module structure, compatible via the algebra structure induced by $f$, to each open $U$ of $X$, with $R$-linear restrictions satisfying the semilinearity $F.\mathrm{res}(a \cdot x) = (\mathrm{res}\,a)\cdot \mathrm{res}\,x$ and the usual functoriality; $F$ is assumed coherent (each $F(U)$ finite over $\Gamma(X,U)$ for $U$ affine) and quasicoherent (on each affine $U$ and each $a \in \Gamma(X,U)$, every section over the basic open of $a$ becomes, after multiplication by a power of $a$, the restriction of a section over $U$, and every section restricting to $0$ is killed by a power of $a$). Let $\psi_n$ be affine-open morphisms from $F$ to the pushforward of the unit presheaf along $g_n$ followed by the first projection, i.e. $R$-linear, $\Gamma(X,U)$-semilinear maps $\psi_{n,U} : F(U) \to \Gamma(Y_n, (g_n \text{ followed by } \mathrm{pr}_1)^{-1}U)$ for affine $U$, compatible with restriction, such that each $\psi_{n,U}$ is surjective with kernel $I^{n+1} \cdot F(U)$, and $\psi_{n,U} = y_n^{*} \circ \psi_{n+1,U}$. Let $A$ be a functor from the opposite of the affine Zariski site of $X$ to commutative rings, $\alpha$ a natural transformation from the restriction of $\mathcal{O}_X$ to that site into $A$ which is coequifibered, $e_U : A(U) \xrightarrow{\sim} F(U)$ additive equivalences carrying multiplication by $\alpha_U(a)$ to the action of $a$ and commuting with restriction, and $r_{n,U} : A(U) \to \Gamma(Y_n, (g_n \text{ followed by } \mathrm{pr}_1)^{-1}U)$ ring homomorphisms with $r_{n,U} = \psi_{n,U} \circ e_U$. Then there exist morphisms $\varphi_n : Y_n \to$ the glued scheme of the relative gluing data of $\alpha$ (the relative spectrum of $A$ over $X$) such that $\varphi_n$ followed by the structure morphism to $X$ equals $g_n$ followed by $\mathrm{pr}_1$; $y_n$ followed by $\varphi_{n+1}$ equals $\varphi_n$; for each $n$ and each affine open $U$ of $X$, the inclusion of the open subscheme $g_n^{-1}(\mathrm{pr}_1^{-1}U)$ followed by $\varphi_n$ equals its canonical morphism to the spectrum of its ring of sections, followed by $\operatorname{Spec}(r_{n,U})$, followed by the chart of the gluing data at $U$; and for each $n$ and $U$ the square of rings with $\alpha_U : \Gamma(X,U) \to A(U)$ and $\mathrm{pr}_1^{*} : \Gamma(X,U) \to \Gamma(X_n, \mathrm{pr}_1^{-1}U)$ on one side, and $r_{n,U}$ and $g_n^{*}$ on the other, is a pushout.
--
--   This is the geometric half of the algebraisation (formal GAGA) step for finite morphisms over an $I$-adically complete base: the levelwise finite schemes $Y_n$ over the truncations $X_n$ are identified with the truncations of the relative spectrum of the algebraised algebra $A$, the identification being expressed by the pushout squares $\Gamma(Y_n, \cdot) = A(U) \otimes_{\Gamma(X,U)} \Gamma(X_n, \cdot)$. It feeds the existence theorems producing a finite morphism over $X$ from a compatible system of finite morphisms over the truncations, in the proper and in the closed-immersion-projection cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered
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
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    (hψk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (hψc : ∀ (n : ℕ) (U : X.affineOpens) (x : F.obj U.1),
      (ψ n).app U x =
        ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom
          ((ψ (n + 1)).app U x))

    (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
    (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A) (Hco : α.Coequifibered)
    (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1)
    (hlin : ∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
      e U ((α.app (op U)).hom a * x) = a • e U x)
    (hnat : ∀ (U V : X.AffineZariskiSite) (i : V ⟶ U) (x : A.obj (op U)),
      e V ((A.map i.op).hom x) = F.res (Scheme.AffineZariskiSite.toOpens_mono i.le) (e U x))
    (r : ∀ (n : ℕ) (U : X.AffineZariskiSite), A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1))
    (hr : ∀ (n : ℕ) (U : X.AffineZariskiSite) (x : A.obj (op U)), r n U x = (ψ n).app ⟨U.1, U.2⟩ (e U x)) :
    ∃ φ : ∀ n : ℕ, Y n ⟶ (Scheme.AffineZariskiSite.relativeGluingData Hco).glued,
      (∀ n : ℕ, φ n ≫ (Scheme.AffineZariskiSite.relativeGluingData Hco).toBase = g n ≫ pullback.fst f (sR n)) ∧
      (∀ n : ℕ, yn n ≫ φ (n + 1) = φ n) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        ((g n) ⁻¹ᵁ ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).ι ≫ φ n =
          ((g n) ⁻¹ᵁ ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (r n U)) ≫
            (Scheme.AffineZariskiSite.relativeGluingData Hco).cover.f U) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        IsPushout (α.app (op U)) ((pullback.fst f (sR n)).app U.1) (CommRingCat.ofHom (r n U))
          ((g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1))) := by sorry
