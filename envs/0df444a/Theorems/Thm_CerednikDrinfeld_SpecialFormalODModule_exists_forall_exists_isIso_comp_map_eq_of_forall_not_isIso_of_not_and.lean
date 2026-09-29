-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f857d2d5-f43d-56de-adb7-b9d1a20dd96d
-- title:
--   First-order deformations at a smooth point are rescalings
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, and let $j_0 : W(\mathbb{F}_{q^2}) \to k$ be a ring homomorphism. Let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ with respect to $j_0$: a commutative two-dimensional formal group law over $k$ equipped with an action of $W(\mathbb{F}_{q^2})$ by formal-group endomorphisms and an endomorphism $\varpi$ with $\varpi \circ \varpi = [q]$ and $\varpi \circ a = \mathrm{Frob}(a) \circ \varpi$, such that the eigenspaces `lieZero` and `lieOne` of the action on the Lie module (where $a$ acts by $j_0(a)$, resp. by $j_0(\mathrm{Frob}\,a)$) are complementary and invertible, and such that $[q]$ has kernel of degree $q^4$. Assume that the linear part of $\varpi$, viewed as a matrix acting by `mulVecLin`, does not annihilate all of `lieZero` and all of `lieOne` simultaneously. Let $X_1$ be a formal $\mathcal{O}_D$-module over the dual numbers $k[\varepsilon]$ together with an isomorphism $w_1$ from the base change of $X_1$ along $k[\varepsilon] \to k$ to $X_0$, and assume $X_1$ is non-trivial in the sense that no morphism of formal $\mathcal{O}_D$-modules from $X_1$ to the base change of $X_0$ along $k \to k[\varepsilon]$ is an isomorphism. Let $(X, w)$ be a further such pair, with $w$ an isomorphism from the reduction of $X$ to $X_0$. Then there is a scalar $c \in k$ such that for every ring endomorphism $\mu$ of $k[\varepsilon]$ which induces the identity on $k$ (i.e. composing $\mu$ with the projection to $k$ gives the projection) and satisfies $\mathrm{snd}(\mu(t)) = c \cdot \mathrm{snd}(t)$ for all $t$, there exists an isomorphism $v$ from $X$ to the base change of $X_1$ along $\mu$ whose reduction along $k[\varepsilon] \to k$, followed by $w_1$, equals $w$ as a pair of power series.
--
--   This expresses, in the language of deformations rather than of explicit structure constants, that at a smooth point the tangent space to the deformation functor of a special formal $\mathcal{O}_D$-module of height $4$ is a line: any fixed non-trivial first-order deformation, rescaled by some $c \in k$, realises every other first-order deformation compatibly with the identifications of the special fibre with $X_0$. It rests on the tangent chart at a smooth point, which is injective on isomorphism classes of deformations and homogeneous under rescaling of $\varepsilon$, and is used in turn to produce one-parameter families of structure constants with prescribed first-order behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (X₁ : FormalODModule q (DualNumber k))
    (w₁ : (X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw₁ : w₁.IsIso)
    (h₁ : ∀ θ : X₁.Hom (X₀.toFormalODModule.map (algebraMap k (DualNumber k))), ¬ θ.IsIso)
    (X : FormalODModule q (DualNumber k))
    (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    ∃ c : k, ∀ (μ : DualNumber k →+* DualNumber k),
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp μ = (TrivSqZeroExt.fstHom k k k).toRingHom →
      (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
      ∃ v : X.Hom (X₁.map μ), v.IsIso ∧
        w₁.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = w.toSeries := by sorry
