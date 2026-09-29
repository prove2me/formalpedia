-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered
-- name    : AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a7e94bba-cc47-5e51-9350-6b2782ca9cd6
-- title:
--   Levelwise morphisms into the relative spectrum of A
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I \subseteq R$ an ideal with $R$ $I$-adically complete, and let $f : X \to \operatorname{Spec} R$ be a proper morphism of schemes. Suppose given, for each $n$, the morphism $s_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ induced by the quotient map, transition morphisms $t_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec}(R/I^{n+2})$ with $t_n \circ s_{n+1} = s_n$, and morphisms $x_n : X_n \to X_{n+1}$ between the fibre products $X_n := X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ which commute with the first projections to $X$ and which over $\operatorname{Spec}(R/I^{n+1})$ are the second projection followed by $t_n$. Further, let $g_n : Y_n \to X_n$ be finite morphisms and $y_n : Y_n \to Y_{n+1}$ morphisms such that each square $(y_n, g_n, g_{n+1}, x_n)$ is a pullback. Let $F$ be an `OModulePresheaf` for $f$: an assignment $U \mapsto F(U)$ of $R$-modules, each also a $\Gamma(X,U)$-module compatibly with the $R$-algebra structure coming from $f$, together with $R$-linear restriction maps satisfying the usual semilinearity, reflexivity and transitivity identities. Let $\psi_n$ be an `AffHom` from $F$ to the pushforward of the unit presheaf along $h_n := g_n$ followed by the projection $X_n \to X$, that is, for each affine open $U \subseteq X$ an $R$-linear map $F(U) \to \Gamma(Y_n, h_n^{-1}U)$ which is semilinear over $\Gamma(X,U)$ and natural in affine opens; assume the compatibility $\psi_n = y_n^* \circ \psi_{n+1}$ on sections over each affine open of $X$. Finally, let $A$ be a presheaf of commutative rings on the affine Zariski site of $X$, let $\alpha$ be a morphism from the restriction of $\mathcal O_X$ to that site into $A$ with $\alpha$ coequifibered, let $e_U : A(U) \simeq F(U)$ be additive bijections satisfying $e_U(\alpha_U(a)\,x) = a \cdot e_U(x)$ and compatible with the restriction maps of $A$ and $F$, and let $r_{n,U} : A(U) \to \Gamma(Y_n, h_n^{-1}U)$ be ring homomorphisms with $r_{n,U}(x) = \psi_n(e_U(x))$. The conclusion asserts the existence of morphisms $\varphi_n : Y_n \to \operatorname{Spec}_X A$, the glued scheme of the relative gluing data attached to $\alpha$, such that $\varphi_n$ followed by the structure morphism to $X$ equals $h_n$, such that $y_n$ followed by $\varphi_{n+1}$ equals $\varphi_n$, and such that for every affine open $U$ of $X$ the inclusion of the open subscheme $h_n^{-1}U \subseteq Y_n$ followed by $\varphi_n$ equals its canonical morphism to $\operatorname{Spec}\Gamma(Y_n, h_n^{-1}U)$ followed by $\operatorname{Spec}(r_{n,U})$ followed by the corresponding chart of the gluing data.
--
--   This is the comparison step in the formal GAGA argument for finite morphisms: a compatible system of finite schemes over the $I$-adic truncations of $X$, together with a quasi-coherent algebra structure presented by $(A,\alpha,e,r)$, gives compatible morphisms into the relative spectrum of that algebra with a prescribed description over affine opens of $X$. It is used in the companion statement that additionally records the resulting squares as pushouts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered
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

    (F : OModulePresheaf f)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
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
            (Scheme.AffineZariskiSite.relativeGluingData Hco).cover.f U) := by sorry
