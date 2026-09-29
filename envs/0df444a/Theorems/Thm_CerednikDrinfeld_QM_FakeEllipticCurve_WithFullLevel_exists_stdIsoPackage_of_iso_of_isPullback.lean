-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_stdIsoPackage_of_iso_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_stdIsoPackage_of_iso_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3a32dde4-f5f0-53b1-9ac6-a527a9ff87d1
-- title:
--   Isomorphism of base changes yields standard pullback isomorphism package
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (an order maximal among orders), together with $N,m\in\mathbb{N}$, a noetherian commutative ring $R$ and a commutative $R$-algebra $L$ (both in `Type 0`). Let $u,w$ be fake elliptic curves over $R$ with $\Lambda$-action, level-$N$ datum and full level-$m$ structure, i.e. pairs consisting of a `FakeEllipticCurve Λ N R` (a scheme $A$ with structure morphism $f$ to $\operatorname{Spec} R$, a relative commutative group law $L$ on its functor of points, abelian-scheme property bundle, fibres of dimension $2$, an action `act` of $\Lambda$ compatible with $f$, the group law, addition, multiplication and traces, and a level scheme $C$ with $\mathrm{lev}:C\to A$) and a `FullLevel m` structure, whose datum is a section $P$ of $f$ killed by $m$, generating the $m$-torsion of every geometric fibre under $\Lambda$, with annihilator $m\Lambda$. Let $u',w'$ be objects of the same kind over $L$, and assume `WithFullLevel.IsPullback (algebraMap R L)` holds for $(u,u')$ and for $(w,w')$: there are morphisms $g$ exhibiting $u'.f$ (resp. $w'.f$) as a pullback of $u.f$ (resp. $w.f$) along $\operatorname{Spec}(L)\to\operatorname{Spec}(R)$, compatible with the group laws on points, with the $\Lambda$-actions, carrying points factoring through the level morphism to points factoring through it downstairs, and sending the full-level section of $u'$ to the base change of that of $u$. Assume further the project's relation `WithFullLevel.Iso u' w'`. Then there are an isomorphism $e$ between the Mathlib pullbacks $A_u\times_{\operatorname{Spec} R}\operatorname{Spec} L$ and $A_w\times_{\operatorname{Spec} R}\operatorname{Spec} L$ and a proof that $e$ lies over $\operatorname{Spec} L$ (its second projections agree), such that: (i) for every scheme $T'$ over $\operatorname{Spec} L$ and all points $x,y$ of the base-changed family, composing the base-changed group-law product of $x$ and $y$ with $e$ equals the base-changed product of $x\circ e$ and $y\circ e$ for $w$; (ii) for every $x\in\Lambda$, $e$ intertwines the endomorphisms of the two pullbacks induced by $u.\mathrm{act}\,x$ and $w.\mathrm{act}\,x$; (iii) $e$ carries the canonical lift of $u$'s full-level section $P$ to that of $w$; and (iv) there exist morphisms $c$ and $c'$ between the pullbacks of the composites $\mathrm{lev}\circ f$ for $u$ and $w$ in both directions, compatible with the base-changed level morphisms and with $e$, respectively $e^{-1}$.
--
--   This is the step converting an isomorphism between two relation-style base changes of fake elliptic curves with full level-$m$ structure into the package of compatibilities (group law, quaternionic action, full-level section, level scheme in both directions) for the standard categorical pullbacks along $\operatorname{Spec} L\to\operatorname{Spec} R$, the shape in which such data are transported in the descent arguments underlying the Čerednik–Drinfeld uniformisation of Shimura curves. It is used by the passage to a finitely generated subalgebra of $L$ over which the isomorphism already exists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_stdIsoPackage_of_iso_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_stdIsoPackage_of_iso_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (u' w' : FakeEllipticCurve.WithFullLevel Λ N m L)
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) u u')
    (hw : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) w w')
    (he : FakeEllipticCurve.WithFullLevel.Iso u' w') :
    ∃ (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
      (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))),
      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))),
        ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
          ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t
            ⟨x.1 ≫ e.hom, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, e_snd, y.2]⟩).1) ∧
      (∀ x : ↥Λ,
        pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ e.hom =
          e.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc, w.1.act_over x, pullback.condition])) ∧
      (pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (u.2.P).1) (𝟙 _)
            (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ e.hom =
          pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (w.2.P).1) (𝟙 _)
            (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp])) ∧
      (∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom) ∧
      (∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv) := by sorry
