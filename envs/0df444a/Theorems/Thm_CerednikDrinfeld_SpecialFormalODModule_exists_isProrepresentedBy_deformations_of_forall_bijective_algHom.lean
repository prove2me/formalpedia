-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations_of_forall_bijective_algHom
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations_of_forall_bijective_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/c5f59e4d-9fc8-5180-9c53-fbe0b542696d
-- title:
--   Universal formal mathcal O_D-module over a pro-representing ring
-- statement:
--   Fix a prime $q$ and a commutative local ring $O$ whose residue field has characteristic $q$, together with a ring homomorphism $\iota\colon \mathbb{Z}_{q^2} = W(\mathbb{F}_{q^2}) \to O$ and a special formal $\mathcal O_D$-module $X_0$ of height $4$ over the residue field of $O$, taken with respect to the composite of $\iota$ with the residue map; here a `FormalODModule` over a ring $B$ is a two-dimensional commutative formal group law $F$ over $B$ equipped with an action of $\mathbb{Z}_{q^2}$ by endomorphisms of $F$ which is multiplicative, additive via $F$ and unital, and with a further endomorphism $\varpi$ of $F$ satisfying $\varpi\circ\varpi = [q]$ and $\varpi\circ[a] = [\varphi(a)]\circ\varpi$ for the Witt vector Frobenius $\varphi$. Let $R$ be a Noetherian local $O$-algebra, complete for the adic topology of its maximal ideal, with a ring homomorphism $\mathrm{res}_R\colon R \to k$ to the residue field $k$ of $O$ restricting to the residue map of $O$. Call a deformation over an Artinian local $O$-algebra $A$ endowed with a surjection $\mathrm{res}_A\colon A \to k$ restricting to the residue map of $O$ a pair $(X, w)$ with $X$ a formal $\mathcal O_D$-module over $A$ and $w$ a homomorphism from the base change $X \otimes_{\mathrm{res}_A} k$ to $X_0$ admitting a two-sided inverse. Assume given, for all such $A$, $\mathrm{res}_A$ and all deformations $(X,w)$, an $O$-algebra map $\beta_A(X,w)\colon R \to A$ such that: $\mathrm{res}_A\circ\beta_A(X,w) = \mathrm{res}_R$; $\beta_A(X,w) = \beta_A(X',w')$ whenever some isomorphism $v\colon X \to X'$ satisfies $w' \circ (v \otimes_{\mathrm{res}_A} k) = w$ on underlying power series tuples; $\beta_{A'}(X \otimes_f A', w') = f\circ\beta_A(X,w)$ for every $O$-algebra map $f\colon A \to A'$ with $\mathrm{res}_{A'}\circ f = \mathrm{res}_A$ and every $w'$ with the same underlying series as $w$; conversely $\beta_A(X,w) = \beta_A(X',w')$ implies the existence of such an isomorphism $v$; and every $O$-algebra map $\chi\colon R \to A$ with $\mathrm{res}_A\circ\chi = \mathrm{res}_R$ is of the form $\beta_A(X,w)$. The conclusion is that there are a formal $\mathcal O_D$-module $\mathcal X$ over $R$ and an isomorphism $w_u$ from $\mathcal X \otimes_{\mathrm{res}_R} k$ to $X_0$ such that for every $A$, $\mathrm{res}_A$ as above and every deformation $(X,w)$ over $A$ there is exactly one $O$-algebra map $\chi\colon R \to A$ with $\mathrm{res}_A\circ\chi = \mathrm{res}_R$ for which some isomorphism $v\colon \mathcal X \otimes_\chi A \to X$ satisfies $w \circ (v \otimes_{\mathrm{res}_A} k) = w_u$ on underlying series.
--
--   This is the effectivity step in the deformation theory of special formal $\mathcal O_D$-modules: it upgrades an abstract isomorphism between the functor of deformation classes of $X_0$ on Artinian local $O$-algebras and the functor of $O$-algebra points of $R$ into an honest universal object over the complete local ring $R$, in the style of Schlessinger's theory of functors of Artin rings. It is used by [`CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations), and the proof cites the pullback-gluing statement [`CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations_of_forall_bijective_algHom.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal IsLocalRing in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations_of_forall_bijective_algHom
    {q : ℕ} [Fact q.Prime]
    (O : Type u) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) q]
    (ι : Zp2 q →+* O) (X₀ : SpecialFormalODModule q ((residue O).comp ι))
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (maximalIdeal R) R]
    (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)
    (β : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso → (R →ₐ[O] A))
    (hβ_res : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso),
      resA.comp (β A resA hs hc X w hw).toRingHom = resR)
    (hβ_iso : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso)
        (X' : FormalODModule q A) (w' : (X'.map resA).Hom X₀.toFormalODModule) (hw' : w'.IsIso)
        (v : X.Hom X'), v.IsIso → w'.toSeries.comp (v.toSeries.map resA) = w.toSeries →
      β A resA hs hc X w hw = β A resA hs hc X' w' hw')
    (hβ_nat : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
        (hc' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA →
      ∀ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso)
        (w' : ((X.map f.toRingHom).map resA').Hom X₀.toFormalODModule) (hw' : w'.IsIso),
        w'.toSeries = w.toSeries →
      β A' resA' hs' hc' (X.map f.toRingHom) w' hw' = f.comp (β A resA hs hc X w hw))
    (hβ_inj : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso)
        (X' : FormalODModule q A) (w' : (X'.map resA).Hom X₀.toFormalODModule) (hw' : w'.IsIso),
      β A resA hs hc X w hw = β A resA hs hc X' w' hw' →
      ∃ v : X.Hom X', v.IsIso ∧ w'.toSeries.comp (v.toSeries.map resA) = w.toSeries)
    (hβ_surj : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (χ : R →ₐ[O] A), resA.comp χ.toRingHom = resR →
      ∃ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso),
        β A resA hs hc X w hw = χ) :
    ∃ (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (_ : wu.IsIso),
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O), Function.Surjective resA →
          resA.comp (algebraMap O A) = residue O →
        ∀ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
          ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧
            ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
              (w.comp (v.map resA)).toSeries = wu.toSeries := by sorry
