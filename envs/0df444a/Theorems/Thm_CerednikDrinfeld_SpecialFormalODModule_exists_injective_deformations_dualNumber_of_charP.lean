-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_of_charP
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/bc5fc868-4b62-5537-9a27-9d5c63b7c9c1
-- title:
--   Finite coordinates on first-order deformations of a special formal 𝒪_D-module
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $j_0 : \mathrm{Zp2}\,q \to k$ a ring homomorphism from the Witt vectors of the field with $q^2$ elements. Let $X_0$ be a `SpecialFormalODModule` for $j_0$: a $2$-dimensional commutative formal group law over $k$ equipped with a $\mathrm{Zp2}\,q$-action and an endomorphism $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ a=\mathrm{Frob}(a)\circ\varpi$, subject to the predicates `IsSpecial` for $j_0$ and `HasHeight 4`. The assertion is that there are an $r\in\mathbb{N}$ and a function $e$ assigning an element of $k^r$ (indexed by `Fin r`) to each triple consisting of a formal $\mathcal{O}_D$-module $X$ over the dual numbers $k[\varepsilon]$, a homomorphism $w$ from the base change of $X$ along $\varepsilon\mapsto 0$ to $X_0$, and a proof that $w$ is an isomorphism, such that: (i) $e(X,w)=e(X',w')$ whenever there is an isomorphism $v:X\to X'$ with $w'\circ(v\bmod\varepsilon)=w$ on underlying power-series tuples; (ii) conversely, equality of the $e$-values produces such an isomorphism $v$; (iii) for $c\in k$ and a ring endomorphism $\mu$ of $k[\varepsilon]$ over $k$ with $\mathrm{snd}(\mu t)=c\,\mathrm{snd}(t)$, one has $e(X_\mu,w')=c\cdot e(X,w)$ whenever $w'$ has the same underlying series as $w$; and (iv) for every commutative ring $B$ with a surjective local homomorphism $\mathrm{res}_B:B\to k$, homomorphisms $p_1,p_2,\sigma:B\to k[\varepsilon]$ lifting $\mathrm{res}_B$ with $\mathrm{snd}(\sigma b)=\mathrm{snd}(p_1 b)+\mathrm{snd}(p_2 b)$, and every $Y$ over $B$ with an isomorphism $u$ from $Y\otimes_{\mathrm{res}_B}k$ to $X_0$, the base changes along $\sigma,p_1,p_2$, rigidified by isomorphisms whose underlying series equal that of $u$, satisfy $e(Y_\sigma)=e(Y_{p_1})+e(Y_{p_2})$.
--
--   This is Schlessinger's condition (H3) — finite-dimensionality of the tangent space of the deformation functor of $X_0$ — formulated through an injective, homogeneous and additive system of coordinates on isomorphism classes of first-order deformations, so that no vector space structure on the set of classes need be constructed beforehand. It feeds the prorepresentability statement [`CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations) for the deformation functor of a special formal $\mathcal{O}_D$-module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_of_charP.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_of_charP
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    ∃ (r : ℕ) (e : ∀ (X : FormalODModule q (DualNumber k))
        (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule),
        w.IsIso → (Fin r → k)),

      (∀ (X : FormalODModule q (DualNumber k))
          (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber k))
          (w' : (X'.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso) (v : X.Hom X'), v.IsIso →
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = w.toSeries →
        e X w hw = e X' w' hw') ∧

      (∀ (X : FormalODModule q (DualNumber k))
          (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber k))
          (w' : (X'.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso),
        e X w hw = e X' w' hw' →
        ∃ v : X.Hom X', v.IsIso ∧
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = w.toSeries) ∧

      (∀ (c : k) (μ : DualNumber k →+* DualNumber k),
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp μ = (TrivSqZeroExt.fstHom k k k).toRingHom →
          (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ (X : FormalODModule q (DualNumber k))
          (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (w' : ((X.map μ).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso), w'.toSeries = w.toSeries →
        e (X.map μ) w' hw' = c • e X w hw) ∧

      (∀ (B : Type u) [CommRing B] (resB : B →+* k), Function.Surjective resB → IsLocalHom resB →
        ∀ (p₁ p₂ σ : B →+* DualNumber k),
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp p₁ = resB →
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp p₂ = resB →
          (TrivSqZeroExt.fstHom k k k).toRingHom.comp σ = resB →
          (∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule), u.IsIso →
        ∀ (w₁ : ((Y.map p₁).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw₁ : w₁.IsIso)
          (w₂ : ((Y.map p₂).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hw₂ : w₂.IsIso)
          (wσ : ((Y.map σ).map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule)
          (hwσ : wσ.IsIso),
          w₁.toSeries = u.toSeries → w₂.toSeries = u.toSeries → wσ.toSeries = u.toSeries →
        e (Y.map σ) wσ hwσ = e (Y.map p₁) w₁ hw₁ + e (Y.map p₂) w₂ hw₂) := by sorry
