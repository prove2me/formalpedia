-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_iso_of_stdIsoPackage
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_iso_of_stdIsoPackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/2831b06f-749b-575e-9eb1-61616337953b
-- title:
--   Isomorphism of standard base changes yields isomorphic base changes
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,m$, a commutative ring $R$ and a commutative $R$-algebra $L$. Let $u,w$ be objects of `FakeEllipticCurve.WithFullLevel` $\Lambda$ $N$ $m$ $R$, i.e. fake elliptic curves over $R$ (a scheme $A\to\operatorname{Spec}R$ with a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms and a level scheme $C$ with structure morphism `lev`) each equipped with a full level-$m$ structure. Write $\pi$ for $\operatorname{Spec}$ of the structure map $R\to L$. Assume given an isomorphism $e$ between the fibre products $u.A\times_{\operatorname{Spec}R}\operatorname{Spec}L$ and $w.A\times_{\operatorname{Spec}R}\operatorname{Spec}L$ such that: $e$ commutes with the second projections; for every scheme $T'$ over $\operatorname{Spec}L$, $e$ takes products of $T'$-points under the base-changed group law of $u$ to products of their images under that of $w$; $e$ intertwines, for each $x\in\Lambda$, the pulled-back endomorphisms `act` $x$ of the two fibre products; $e$ carries the pulled-back full-level section of $u$ to that of $w$; and the canonical maps from the base-changed level schemes are compatible with $e$ and with $e^{-1}$ through suitable morphisms $c$, $c'$ between $\operatorname{pullback}(u.\mathrm{lev}\circ u.f,\pi)$ and $\operatorname{pullback}(w.\mathrm{lev}\circ w.f,\pi)$. The conclusion asserts the existence of $u_L,w_L$ over $L$ with `WithFullLevel.IsPullback` for $R\to L$ relating $u$ to $u_L$ and $w$ to $w_L$ (a morphism $u_L.A\to u.A$ forming a pullback square over $\pi$, compatible with group laws, $\Lambda$-actions, factorisation through `lev` and the full-level sections, and likewise for $w$), together with `WithFullLevel.Iso` $u_L$ $w_L$: an isomorphism $u_L.A\cong w_L.A$ over $\operatorname{Spec}L$ respecting group laws, $\Lambda$-actions, factorisation through the level morphisms in both directions, and the full-level sections.
--
--   This converts data attached to the standard categorical fibre products over $\operatorname{Spec}L$ into the project's intrinsic formulation, producing genuine base changes $u_L,w_L$ of the two fake elliptic curves with full level structure and an isomorphism between them. It is used in `exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback`, the step descending an isomorphism of fake elliptic curves to a finitely generated subalgebra in the Čerednik–Drinfel'd part of the development, and it relies on `exists_isPullback_levelIff` for the existence of base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_iso_of_stdIsoPackage.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_iso_of_stdIsoPackage
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R)
    (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_mul : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))),
      ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
        ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, e_snd, y.2]⟩).1)
    (e_act : ∀ x : ↥Λ,
      pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ e.hom =
        e.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, w.1.act_over x, pullback.condition]))
    (e_P : pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (u.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ e.hom =
        pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (w.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp]))
    (e_lev : ∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_lev' : ∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv) :
    ∃ (uL wL : FakeEllipticCurve.WithFullLevel Λ N m L),
      FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) u uL ∧
      FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) w wL ∧
      FakeEllipticCurve.WithFullLevel.Iso uL wL := by sorry
