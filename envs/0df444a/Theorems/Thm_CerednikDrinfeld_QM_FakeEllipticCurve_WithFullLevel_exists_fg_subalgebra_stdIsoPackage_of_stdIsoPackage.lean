-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/fcd60124-39b5-5bc7-a1b7-0626d8c01cc8
-- title:
--   Descent of a full-level isomorphism package to a f.g. subalgebra
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders, together with naturals $N,m$, a noetherian commutative ring $R$ and a commutative $R$-algebra $L$. Let $u,w$ be elements of `FakeEllipticCurve.WithFullLevel Λ N m R`, i.e. pairs consisting of a fake elliptic curve over $R$ (a scheme $A$ with structure morphism $f$ to $\operatorname{Spec} R$, a relative group law $L$ on its points, a $\Lambda$-action `act`, a level datum `lev`, and the remaining axioms of the structure) and a full level-$m$ structure on it, whose component `P` is a point of $A$ over $\operatorname{Spec} R$. Write all base changes as Mathlib pullbacks along $\operatorname{Spec}$ of the structure map. Assume given an isomorphism $e$ between the base changes of $u.1.f$ and $w.1.f$ to $L$ such that: $e$ is a morphism over $\operatorname{Spec} L$, i.e. $e$ followed by the second projection for $w$ is the second projection for $u$; composition with $e$ turns the product of any two points of the base-changed $u$, over any $t:T'\to\operatorname{Spec} L$, under `u.1.L.baseChange`, into their images' product under `w.1.L.baseChange`; $e$ intertwines the base-changed actions of every $x\in\Lambda$; $e$ carries the base-changed section $u.2.P$ to $w.2.P$; and there exist morphisms $c$, $c'$ between the base changes of $u.1.\mathrm{lev}\circ u.1.f$ and $w.1.\mathrm{lev}\circ w.1.f$ in both directions making the level data compatible with $e.\mathrm{hom}$ and $e.\mathrm{inv}$ respectively. Then for every finite subset $s\subseteq L$ there is a finitely generated $R$-subalgebra $T\subseteq L$ containing $s$, an isomorphism $e_T$ between the base changes of $u.1.f$ and $w.1.f$ to $T$ over $\operatorname{Spec} T$, and the same five compatibilities (group law, $\Lambda$-action, full-level section, and the two level morphisms) with $L$ replaced by $T$. No compatibility between $e_T$ and $e$ is asserted.
--
--   This is the limit-and-approximation step (in the style of EGA IV, §8.8) by which an isomorphism of fake elliptic curves with $\Lambda$-action, level-$N$ and full level-$m$ structure over a base change to a possibly large $R$-algebra $L$ is realised already over a finitely generated $R$-subalgebra, using that the relevant structure morphisms are quasi-compact, quasi-separated and locally of finite presentation, respectively locally of finite type. It feeds the representability argument for the Čerednik–Drinfeld fine moduli problem, and is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
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
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv)
    (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (eT : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (eT_snd : eT.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))),
        (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))),
          ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))).mul t x y).1 ≫ eT.hom =
            ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))).mul t
              ⟨x.1 ≫ eT.hom, by rw [Category.assoc, eT_snd, x.2]⟩ ⟨y.1 ≫ eT.hom, by rw [Category.assoc, eT_snd, y.2]⟩).1) ∧
        (∀ x : ↥Λ,
          pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
              (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ eT.hom =
            eT.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
              (by rw [Category.assoc, w.1.act_over x, pullback.condition])) ∧
        (pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ (u.2.P).1) (𝟙 _)
              (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ eT.hom =
            pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ (w.2.P).1) (𝟙 _)
              (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp])) ∧
        (∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.hom) ∧
        (∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.inv) := by sorry
