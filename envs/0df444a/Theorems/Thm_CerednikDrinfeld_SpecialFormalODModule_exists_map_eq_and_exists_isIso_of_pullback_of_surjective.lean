-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/6bfe3968-b3f3-5df1-ad3e-eafe09452a08
-- title:
--   Gluing deformations of a special formal 𝒪_D-module
-- statement:
--   Let $q$ be a prime and $k$ a field of characteristic $q$, let $j_0\colon W(\mathbb{F}_{q^2})\to k$ be a ring homomorphism (here `Zp2 q` is the Witt vectors of the field `GaloisField q 2`), and let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ relative to $j_0$, i.e. a two-variable commutative formal group law over $k$ equipped with an action of `Zp2 q` by pairs of power series and a series $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[a^{\sigma}]\circ\varpi$, satisfying the predicates `IsSpecial j₀` and `HasHeight 4`. Let $p'\colon B\to A'$, $p''\colon B\to A''$, $q'\colon A'\to A$, $q''\colon A''\to A$ be homomorphisms of commutative rings with $q'\circ p'=q''\circ p''$ and such that for all $a'\in A'$, $a''\in A''$ with $q'(a')=q''(a'')$ there is a unique $b\in B$ with $p'(b)=a'$ and $p''(b)=a''$ (so the square is elementwise cartesian); assume $q''$ surjective and a local homomorphism. Let $\mathrm{res}_B,\mathrm{res}_{A'},\mathrm{res}_{A''},\mathrm{res}_A$ be homomorphisms to $k$ with $\mathrm{res}_{A'}\circ p'=\mathrm{res}_B$, $\mathrm{res}_{A''}\circ p''=\mathrm{res}_B$, $\mathrm{res}_A\circ q'=\mathrm{res}_{A'}$, $\mathrm{res}_A\circ q''=\mathrm{res}_{A''}$, with $\mathrm{res}_A$ surjective and $\ker(\mathrm{res}_A)$ nilpotent. Two assertions are concluded. First: given formal $\mathcal{O}_D$-modules $X'$ over $A'$ and $X''$ over $A''$ with invertible $\mathcal{O}_D$-homomorphisms $w'\colon X'\otimes_{\mathrm{res}_{A'}}k\to X_0$ and $w''\colon X''\otimes_{\mathrm{res}_{A''}}k\to X_0$, and an invertible $\mathcal{O}_D$-homomorphism $\varphi\colon X'\otimes_{q'}A\to X''\otimes_{q''}A$ with $w''\circ(\varphi\otimes_{\mathrm{res}_A}k)=w'$ as pairs of power series over $k$, there are a formal $\mathcal{O}_D$-module $Y$ over $B$ and an invertible $u\colon Y\otimes_{\mathrm{res}_B}k\to X_0$ with $Y\otimes_{p'}A'=X'$ (equality of formal $\mathcal{O}_D$-modules), with $u$ given by the same series as $w'$, and an invertible $v\colon Y\otimes_{p''}A''\to X''$ whose series maps under $q''$ to that of $\varphi$ and satisfies $w''\circ(v\otimes_{\mathrm{res}_{A''}}k)=u$. Second: given $Y_1,Y_2$ over $B$ with invertible $u_1,u_2$ to $X_0$ after reduction along $\mathrm{res}_B$, and invertible $v'\colon Y_1\otimes_{p'}A'\to Y_2\otimes_{p'}A'$ and $v''\colon Y_1\otimes_{p''}A''\to Y_2\otimes_{p''}A''$ both compatible with $u_1,u_2$ over $k$, there is an invertible $\mathcal{O}_D$-homomorphism $v\colon Y_1\to Y_2$ whose series maps to those of $v'$ and $v''$ under $p'$ and $p''$ and which satisfies $u_2\circ(v\otimes_{\mathrm{res}_B}k)=u_1$.
--
--   This is the gluing property of the deformation functor of a special formal $\mathcal{O}_D$-module along an elementwise cartesian square of coefficient rings with one surjective, unit-reflecting side: in Schlessinger's terms, conditions (H1), (H2) and the strong form of (H4) for that functor, with objects glued in part one and isomorphisms glued in part two. It is used in the computation of the tangent space over dual numbers and in the prorepresentability of the deformation functor, and is deduced from the corresponding statements for bare formal group laws together with a rigidity lemma for homomorphisms agreeing modulo a nilpotent ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
    (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
    (hcomm : q'.comp p' = q''.comp p'')
    (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')
    (hq'' : Function.Surjective q'') (hq''loc : IsLocalHom q'')
    (resB : B →+* k) (resA' : A' →+* k) (resA'' : A'' →+* k) (resA : A →+* k)
    (hresA' : resA'.comp p' = resB) (hresA'' : resA''.comp p'' = resB)
    (hresq' : resA.comp q' = resA') (hresq'' : resA.comp q'' = resA'')
    (hresA : Function.Surjective resA) (hnil : IsNilpotent (RingHom.ker resA)) :
    (∀ (X' : FormalODModule q A') (w' : (X'.map resA').Hom X₀.toFormalODModule), w'.IsIso →
      ∀ (X'' : FormalODModule q A'') (w'' : (X''.map resA'').Hom X₀.toFormalODModule), w''.IsIso →
      ∀ (φ : (X'.map q').Hom (X''.map q'')), φ.IsIso →
        w''.toSeries.comp (φ.toSeries.map resA) = w'.toSeries →
        ∃ (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule), u.IsIso ∧
          Y.map p' = X' ∧ u.toSeries = w'.toSeries ∧
          ∃ v : (Y.map p'').Hom X'', v.IsIso ∧ v.toSeries.map q'' = φ.toSeries ∧
            w''.toSeries.comp (v.toSeries.map resA'') = u.toSeries) ∧
    (∀ (Y₁ : FormalODModule q B) (u₁ : (Y₁.map resB).Hom X₀.toFormalODModule), u₁.IsIso →
      ∀ (Y₂ : FormalODModule q B) (u₂ : (Y₂.map resB).Hom X₀.toFormalODModule), u₂.IsIso →
      ∀ (v' : (Y₁.map p').Hom (Y₂.map p')), v'.IsIso →
        u₂.toSeries.comp (v'.toSeries.map resA') = u₁.toSeries →
      ∀ (v'' : (Y₁.map p'').Hom (Y₂.map p'')), v''.IsIso →
        u₂.toSeries.comp (v''.toSeries.map resA'') = u₁.toSeries →
        ∃ v : Y₁.Hom Y₂, v.IsIso ∧ v.toSeries.map p' = v'.toSeries ∧
          v.toSeries.map p'' = v''.toSeries ∧
          u₂.toSeries.comp (v.toSeries.map resB) = u₁.toSeries) := by sorry
