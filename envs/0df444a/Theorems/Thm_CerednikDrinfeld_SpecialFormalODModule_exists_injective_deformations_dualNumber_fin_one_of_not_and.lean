-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_fin_one_of_not_and
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/24768a41-6a70-5d9b-8608-28120463bddd
-- title:
--   First-order deformations inject into k at a smooth point
-- statement:
--   Let $q$ be a prime, $k$ an algebraically closed field of characteristic $q$, $j_0\colon \mathbb Z_{q^2}=W(\mathbb F_{q^2})\to k$ a ring homomorphism, and $X_0$ a special formal $\mathcal O_D$-module over $k$ relative to $j_0$: a two-dimensional commutative formal group law over $k$ with an action of $\mathbb Z_{q^2}$ and a law endomorphism $\Pi$ satisfying $\Pi\circ\Pi=[q]$ and $\Pi\circ[a]=[\sigma a]\circ\Pi$, whose Lie module is the direct sum of the complementary invertible eigen-submodules $\mathrm{lieZero}$ (where each $a$ acts by $j_0(a)$) and $\mathrm{lieOne}$ (where each $a$ acts by $j_0(\sigma a)$), and with $[q]$ of kernel degree $q^4$. Assume $X_0$ is a smooth point, in the sense that the $2\times2$ matrix of linear coefficients of $\Pi$ does not annihilate both $\mathrm{lieZero}$ and $\mathrm{lieOne}$. Then there is a function $e$ assigning to every formal $\mathcal O_D$-module $X$ over the dual numbers $k[\varepsilon]$ together with an isomorphism $w$ from the reduction $X\otimes_{k[\varepsilon]}k$ to $X_0$ a tuple in $\mathrm{Fin}\,1\to k$, with four properties. First, $e(X,w)=e(X',w')$ whenever there is an isomorphism $v\colon X\to X'$ over $k[\varepsilon]$ with $w'\circ\bar v=w$ on power series. Second, conversely, $e(X,w)=e(X',w')$ forces the existence of such an isomorphism $v$; so $e$ is injective on isomorphism classes of deformations. Third, for $c\in k$ and a ring endomorphism $\mu$ of $k[\varepsilon]$ lifting the identity of $k$ and acting on the $\varepsilon$-part by multiplication by $c$, one has $e(X\otimes_\mu k[\varepsilon],w')=c\cdot e(X,w)$ whenever $w'$ has the same series as $w$. Fourth, additivity: for a commutative ring $B$ with a surjective local homomorphism $\mathrm{res}_B\colon B\to k$, ring homomorphisms $p_1,p_2,\sigma\colon B\to k[\varepsilon]$ lifting $\mathrm{res}_B$ with $\mathrm{snd}\circ\sigma=\mathrm{snd}\circ p_1+\mathrm{snd}\circ p_2$, and a formal $\mathcal O_D$-module $Y$ over $B$ with an isomorphism $u\colon Y\otimes_B k\to X_0$, the three induced deformations rigidified by series equal to that of $u$ satisfy $e(Y\otimes_\sigma k[\varepsilon])=e(Y\otimes_{p_1}k[\varepsilon])+e(Y\otimes_{p_2}k[\varepsilon])$.
--
--   This is the upper bound half of the tangent space computation for Drinfeld's deformation functor of a special formal $\mathcal O_D$-module of height $4$: at a smooth point the space of first-order deformations embeds $k$-linearly (constancy and injectivity on isomorphism classes, homogeneity, additivity) into a one-dimensional $k$-space. It feeds the construction of the rigidifying isomorphisms and the description of the maximal ideal of a prorepresenting ring, the two results that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_fin_one_of_not_and
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ (e : ∀ (X : FormalODModule q (DualNumber k))
        (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule),
        w.IsIso → (Fin 1 → k)),

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
